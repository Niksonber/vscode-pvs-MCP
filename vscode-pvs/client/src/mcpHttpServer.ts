import { spawn, ChildProcess } from 'child_process';
import * as fs from 'fs';
import { Server } from 'http';
import * as path from 'path';
import * as vscode from 'vscode';
import { EventsDispatcher } from './eventsDispatcher';
import {
    ProofCommandResponse,
    ProveFormulaResponse,
    EvaluatorCommandResponse,
    ProveFormulaRequest,
    PvsTheory,
    PvsFormula,
    ProofEditEvent,
    ProofExecEvent,
    ProofStatus,
    PvsVersionDescriptor,
    ServerMode
} from './common/serverInterface';
import { StartXTermEvaluatorRequest } from './views/vscodePvsXTerm';
import { ProveTheoryProgressEvent } from './views/vscodePvsWorkspaceExplorer';
import * as fsUtils from './common/fsUtils';
import * as vscodeUtils from './utils/vscode-utils';

import express from 'express';
import cors from 'cors';
import { McpServer, ResourceTemplate } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import { z } from 'zod';

interface ActiveFormulaSession extends ProveFormulaRequest {
    id?: string;
}

interface ResolvedPvsTarget {
    filePath: string;
    contextFolder: string;
    fileName: string;
    fileExtension: string;
    theoryName: string;
    formulaName?: string;
    fileContent: string;
}

interface ProveTheoryJobState {
    jobId: string;
    status: "preparing" | "running" | "completed" | "cancelled" | "failed";
    initiatedBy: "mcp" | "ui";
    filePath: string;
    theoryName: string;
    options: {
        unprovedOnly: boolean;
        useJprf: boolean;
    };
    startedAt: number;
    updatedAt: number;
    completedAt?: number;
    total: number;
    completed: number;
    currentFormula?: string;
    theorems: { theoryName: string; formulaName: string; status: ProofStatus; ms: number }[];
    error?: string;
    cancellationSource?: vscode.CancellationTokenSource;
    completionPromise?: Promise<void>;
    resolveCompletion?: () => void;
}

interface ProveItFormulaResult {
    formula: string;
    status: string;
    rawStatus: string;
    details?: string;
}

interface ProveItGrandTotals {
    totalFormulas: number;
    attempted: number;
    succeeded: number;
    unfinished: number;
    untried: number;
    rawLine: string;
}

interface ProveItJobState {
    jobId: string;
    status: "running" | "completed" | "cancelled" | "failed";
    target: string;
    resolvedTargetArg: string;
    cwd: string;
    proveitPath: string;
    args: string[];
    commandLine: string;
    options: {
        theories?: string[];
        formulas?: string[];
        importchain?: boolean;
        clean?: boolean;
        typecheckOnly?: boolean;
        timeoutSecs?: number;
        force?: boolean;
        scripts?: boolean;
        writeScripts?: boolean;
        autoFix?: number;
        log?: boolean;
        traces?: boolean;
        quiet?: boolean;
        summaryMode?: "md" | "csv";
        extraArgs?: string[];
    };
    startedAt: number;
    updatedAt: number;
    completedAt?: number;
    exitCode: number | null;
    signal: NodeJS.Signals | null;
    stdout: string;
    stderr: string;
    formulas: ProveItFormulaResult[];
    grandTotals?: ProveItGrandTotals;
    summaryFiles: string[];
    error?: string;
    process?: ChildProcess;
    completionPromise?: Promise<void>;
    resolveCompletion?: () => void;
}

const ALLOWED_DOC_TOPICS = ["USER-INTERFACE", "FAQ", "TUTORIAL", "WALKTHROUGH"] as const;

const PVS_MCP_INSTRUCTIONS = [
    "# VSCode-PVS Collaborative Proving Instructions",
    "",
    "This MCP server operates in a shared, human-in-the-loop VS Code environment where both the human user and the AI agent can interact with the PVS prover and evaluator.",
    "",
    "## 1. Synchronizing State When Continuing a Proof",
    "- Because the human user may have manually executed, undone, or modified proof steps in the VS Code UI, never assume the proof is at the last state you saw.",
    "- Whenever you are asked to continue, inspect, or help with an ongoing proof—or before sending mutating proof commands (`(skeep)`, `(grind)`, `(expand ...)`, `(lemma ...)`, etc.) after any user interaction—first call `apply_proof_command` with `(skip)`.",
    "- `(skip)` is a no-op prover command that safely returns the current active sequent, label, and subgoal without altering the proof tree.",
    "- Only call `start_proof` when no proof session is currently active or when explicitly asked to start/restart a proof from the beginning.",
    "",
    "## 2. Searching for Lemmas in Prelude & NASALib",
    "- Before guessing lemma names, call `get_pvs_library_paths` to obtain the local filesystem paths for the PVS Prelude (`prelude.pvs`) and NASALib sub-libraries, then use `grep` or `ripgrep` to find exact lemma names and signatures.",
    "",
    "## 3. Long-Running Operations, `proveit` CLI, & Recovery",
    "- Batch theory proofs in the UI (`prove_theory`) can take several minutes; if `prove_theory` returns with status `running`, poll or wait using `get_prove_theory_status`.",
    "- **CRITICAL (`prove_with_proveit` & `get_proveit_status`):** ONLY use `prove_with_proveit` (and `get_proveit_status`) when the user **explicitly** asks for batch proving, asks to run `proveit`, or asks to prove without the VS Code user interface. For normal interactive proving or standard UI-integrated theory verification, use `start_proof` / `apply_proof_command` or `prove_theory` instead.",
    "- If PVS becomes unresponsive or stuck on a heavy proof command, use `restart_pvs` (prefer `mode: \"interrupt_and_quit\"` first, or `mode: \"reboot\"` if hard-stuck).",
    "",
    "## 4. If user ask for user iterface information, check MCP resource for more information."
].join("\n");

export class McpHttpServer {
    private server: Server | null = null;
    private activeFormula: ActiveFormulaSession | null = null;
    private activeEvaluator: PvsTheory | null = null;
    private currentProveTheoryJob: ProveTheoryJobState | null = null;
    private proveTheoryJobsById: Map<string, ProveTheoryJobState> = new Map();
    private currentProveItJob: ProveItJobState | null = null;
    private proveItJobsById: Map<string, ProveItJobState> = new Map();

    private readonly onProveFormulaResponse = (desc: ProveFormulaResponse): void => {
        if (desc?.req) {
            const proofId = (desc.res && typeof desc.res !== 'string') ? (desc.res.id || "") : "";
            this.activeFormula = {
                ...desc.req,
                id: proofId || this.activeFormula?.id || ""
            };
        }
    };

    private readonly onProofCommandResponse = (desc: ProofCommandResponse): void => {
        if (!desc?.res) {
            return;
        }
        if (desc.res === "Q.E.D." || (typeof desc.res !== "string" && desc.res.status === "quit")) {
            this.activeFormula = null;
        } else if (typeof desc.res !== "string" && desc.res.id && this.activeFormula) {
            this.activeFormula.id = desc.res.id;
        }
    };

    private readonly onProverEvent = (desc: ProofEditEvent | ProofExecEvent): void => {
        if (desc?.action === "did-quit-proof" || desc?.action === "did-fail-to-start-proof") {
            this.activeFormula = null;
        } else if ((desc?.action === "did-load-proof" || desc?.action === "did-open-proof") && desc.formula) {
            this.syncActiveFormulaFromTarget(desc.formula);
        }
    };

    private readonly onServerModeUpdate = (desc: { mode: ServerMode }): void => {
        if (!desc) {
            return;
        }
        if (desc.mode === "in-checker") {
            this.activeEvaluator = null;
            const target = this.eventsDispatcher.xterm?.getTheory() as PvsFormula;
            if (!this.activeFormula && target) {
                this.syncActiveFormulaFromTarget(target);
            }
        } else if (desc.mode === "pvsio") {
            this.activeFormula = null;
            const target = this.eventsDispatcher.xterm?.getTheory();
            if (target) {
                this.activeEvaluator = target;
            }
        } else {
            this.activeFormula = null;
            this.activeEvaluator = null;
        }
    };

    private readonly onEvaluatorCommandResponse = (desc: EvaluatorCommandResponse): void => {
        if (desc?.res === "bye!") {
            this.activeEvaluator = null;
        }
    };

    private readonly onProveTheoryProgress = (evt: ProveTheoryProgressEvent): void => {
        if (!evt || evt.tccsOnly) {
            return;
        }
        this.activeFormula = null;
        this.activeEvaluator = null;

        const now = Date.now();
        let job = this.currentProveTheoryJob;
        const isJobActive = job && (job.status === "preparing" || job.status === "running");

        if (!isJobActive) {
            const jobId = `prove-theory-${now}`;
            const filePath = evt.theory ? fsUtils.desc2fname(evt.theory) : "";
            let resolveCompletion: (() => void) | undefined;
            const completionPromise = new Promise<void>(resolve => {
                resolveCompletion = resolve;
            });
            job = {
                jobId,
                status: evt.phase,
                initiatedBy: "ui",
                filePath,
                theoryName: evt.theory?.theoryName || "",
                options: {
                    unprovedOnly: false,
                    useJprf: false
                },
                startedAt: now,
                updatedAt: now,
                total: evt.total ?? 0,
                completed: evt.completed ?? 0,
                currentFormula: evt.currentFormula,
                theorems: evt.theorems ? [...evt.theorems] : [],
                error: evt.error,
                completionPromise,
                resolveCompletion
            };
            this.currentProveTheoryJob = job;
            this.proveTheoryJobsById.set(jobId, job);
        } else if (job) {
            job.status = evt.phase;
            job.updatedAt = now;
            job.total = evt.total ?? job.total;
            job.completed = evt.completed ?? job.completed;
            job.currentFormula = evt.currentFormula;
            job.theorems = evt.theorems ? [...evt.theorems] : job.theorems;
            if (evt.error) {
                job.error = evt.error;
            }
        }

        if (job && (evt.phase === "completed" || evt.phase === "cancelled" || evt.phase === "failed")) {
            job.completedAt = now;
            job.currentFormula = undefined;
            job.resolveCompletion?.();
        }
    };

    private readonly onProveTheoryResponse = (desc: {
        theory: PvsTheory;
        summary: fsUtils.TheorySummary | null;
        tccsOnly?: boolean;
        cancelled?: boolean;
        error?: string;
    }): void => {
        if (!desc || desc.tccsOnly) {
            return;
        }
        const job = this.currentProveTheoryJob;
        if (!job) {
            return;
        }
        const now = Date.now();
        job.updatedAt = now;
        job.completedAt = job.completedAt || now;
        job.currentFormula = undefined;
        if (desc.summary) {
            job.total = desc.summary.total ?? job.total;
            job.theorems = desc.summary.theorems ? [...desc.summary.theorems] : job.theorems;
            job.completed = job.theorems.length;
        }
        if (job.status === "cancelled" || desc.cancelled) {
            job.status = "cancelled";
        } else if (desc.error) {
            job.status = "failed";
            job.error = desc.error;
        } else if (job.status === "preparing" || job.status === "running") {
            job.status = "completed";
        }
        job.resolveCompletion?.();
    };

    private readonly onPvsServerRebooting = (desc: { msg?: string }): void => {
        this.activeFormula = null;
        this.activeEvaluator = null;
        const job = this.currentProveTheoryJob;
        if (job && (job.status === "preparing" || job.status === "running")) {
            const now = Date.now();
            job.cancellationSource?.cancel();
            job.status = "cancelled";
            job.updatedAt = now;
            job.completedAt = now;
            job.currentFormula = undefined;
            job.error = desc?.msg || "PVS server was restarted";
            job.resolveCompletion?.();
        }
    };

    constructor(private eventsDispatcher: EventsDispatcher) {
        this.registerSessionSyncListeners();
    }

    private registerSessionSyncListeners(): void {
        this.eventsDispatcher.addProveFormulaResponseListener(this.onProveFormulaResponse);
        this.eventsDispatcher.addProofCommandResponseListener(this.onProofCommandResponse);
        this.eventsDispatcher.addProverEventListener(this.onProverEvent);
        this.eventsDispatcher.addServerModeUpdateListener(this.onServerModeUpdate);
        this.eventsDispatcher.addEvaluatorCommandResponseListener(this.onEvaluatorCommandResponse);
        this.eventsDispatcher.addProveTheoryProgressListener(this.onProveTheoryProgress);
        this.eventsDispatcher.addProveTheoryResponseListener(this.onProveTheoryResponse);
        this.eventsDispatcher.addPvsServerRebootingListener(this.onPvsServerRebooting);
    }

    private unregisterSessionSyncListeners(): void {
        this.eventsDispatcher.removeProveFormulaResponseListener(this.onProveFormulaResponse);
        this.eventsDispatcher.removeProofCommandResponseListener(this.onProofCommandResponse);
        this.eventsDispatcher.removeProverEventListener(this.onProverEvent);
        this.eventsDispatcher.removeServerModeUpdateListener(this.onServerModeUpdate);
        this.eventsDispatcher.removeEvaluatorCommandResponseListener(this.onEvaluatorCommandResponse);
        this.eventsDispatcher.removeProveTheoryProgressListener(this.onProveTheoryProgress);
        this.eventsDispatcher.removeProveTheoryResponseListener(this.onProveTheoryResponse);
        this.eventsDispatcher.removePvsServerRebootingListener(this.onPvsServerRebooting);
    }

    private syncActiveFormulaFromTarget(target: PvsFormula | PvsTheory | null | undefined): void {
        if (!target || !target.fileName || !target.theoryName) {
            return;
        }
        const formulaName = (target as PvsFormula).formulaName || this.activeFormula?.formulaName || "";
        if (!formulaName) {
            return;
        }
        this.activeFormula = {
            contextFolder: target.contextFolder,
            fileName: target.fileName,
            fileExtension: target.fileExtension,
            theoryName: target.theoryName,
            formulaName,
            proofFile: {
                contextFolder: target.contextFolder,
                fileName: target.fileName,
                fileExtension: ".jprf"
            },
            id: this.activeFormula?.id || ""
        };
    }

    private resolvePvsTarget(
        rawPath: string,
        options?: {
            theoryName?: string;
            requireFormula?: boolean;
            mustExist?: boolean;
        }
    ): ResolvedPvsTarget {
        if (!rawPath) {
            throw new Error("Missing file or formula path parameter");
        }

        let filePath = rawPath.trim();
        let hashFragment: string | undefined;

        if (filePath.includes('#')) {
            const parts = filePath.split('#');
            filePath = parts[0].trim();
            hashFragment = parts[1]?.trim();
        }

        if (options?.requireFormula && !hashFragment) {
            throw new Error("formula_path must be in the format 'filepath#formula_name'");
        }

        filePath = fsUtils.tildeExpansion(filePath);

        if (options?.mustExist !== false && !fs.existsSync(filePath)) {
            throw new Error(`File not found: ${filePath}`);
        }

        const fileExtension = fsUtils.getFileExtension(filePath);
        const fileName = fsUtils.getFileName(filePath);
        const contextFolder = fsUtils.getContextFolder(filePath);
        const formulaName = options?.requireFormula ? hashFragment : undefined;
        let theoryName = options?.theoryName || (!options?.requireFormula ? hashFragment : undefined);

        let fileContent = "";
        try {
            if (fs.existsSync(filePath)) {
                fileContent = fs.readFileSync(filePath, 'utf8');
            }
        } catch (e) {
            console.error("[mcp-http-server] Error reading PVS file", e);
        }

        if (!theoryName && fileContent) {
            if (formulaName) {
                const escapedFormula = formulaName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
                const declRegex = new RegExp(`^\\s*${escapedFormula}\\s*:`, 'm');
                const match = declRegex.exec(fileContent);
                if (match && match.index !== undefined) {
                    const line = fileContent.substring(0, match.index).split('\n').length;
                    const inferredTheory = fsUtils.findTheoryName(fileContent, line);
                    if (inferredTheory) {
                        theoryName = inferredTheory;
                    }
                }
            }
            if (!theoryName) {
                const match = fileContent.match(/^\s*([a-zA-Z0-9_?]+)\s*:\s*(?:\[[^\]]+\]\s*)?THEORY\b/im);
                if (match) {
                    theoryName = match[1];
                }
            }
        }

        theoryName = theoryName || fileName;
        if (fileExtension === ".tccs" && theoryName.endsWith("_TCCS")) {
            theoryName = theoryName.substring(0, theoryName.length - 5);
        }

        return {
            filePath,
            contextFolder,
            fileName,
            fileExtension,
            theoryName,
            formulaName,
            fileContent
        };
    }

    private async runTypecheck(filePath: string, timeoutMs: number = 60000): Promise<any> {
        const targetFileName = fsUtils.getFileName(filePath);
        const targetContext = fsUtils.getContextFolder(filePath);

        const responsePromise = this.eventsDispatcher.waitForResponse<any>("typecheckFileResponse", {
            timeoutMs,
            filter: (desc) => {
                if (!desc?.args) {
                    return true;
                }
                return desc.args.fileName === targetFileName && desc.args.contextFolder === targetContext;
            }
        });

        await vscode.commands.executeCommand("vscode-pvs.typecheck-file", filePath);
        return await responsePromise;
    }

    private async waitForJobOrTimeout(job: ProveTheoryJobState, timeoutMs: number): Promise<void> {
        if (timeoutMs <= 0 || !job.completionPromise) {
            return;
        }
        if (job.status === "completed" || job.status === "cancelled" || job.status === "failed") {
            return;
        }
        await Promise.race([
            job.completionPromise,
            new Promise<void>(resolve => setTimeout(resolve, timeoutMs))
        ]);
    }

    private formatProveTheoryJobPayload(job: ProveTheoryJobState, extra?: { alreadyRunning?: boolean }) {
        const now = Date.now();
        const endTimestamp = job.completedAt || now;
        const elapsedMs = Math.max(0, endTimestamp - job.startedAt);
        const theorems = job.theorems || [];
        const provedCount = theorems.filter(t => t.status === "proved").length;
        const unprovedCount = theorems.filter(t => t.status !== "proved").length;
        const completed = theorems.length;
        const total = job.total || completed;
        const isRunning = job.status === "preparing" || job.status === "running";
        const remaining = Math.max(0, total - completed);
        const recommendedPollSeconds = remaining > 10 ? 25 : remaining > 3 ? 15 : 10;

        let resultMessage: string;
        if (isRunning) {
            const currentFormulaPart = job.currentFormula ? ` (currently proving '${job.currentFormula}')` : "";
            resultMessage = extra?.alreadyRunning
                ? `A theory proof job (${job.jobId}) is already running for theory '${job.theoryName}': ${completed}/${total} formulas processed${currentFormulaPart}.`
                : `Proving theory '${job.theoryName}' in background (job_id: '${job.jobId}'): ${completed}/${total} formulas processed${currentFormulaPart}.`;
        } else if (job.status === "cancelled") {
            resultMessage = `Theory proof for '${job.theoryName}' was cancelled after ${completed}/${total} formulas (${provedCount} proved, ${unprovedCount} unproved).`;
        } else if (job.status === "failed") {
            resultMessage = `Theory proof for '${job.theoryName}' failed after ${completed}/${total} formulas: ${job.error || "Unknown error"}`;
        } else {
            resultMessage = total === 0
                ? `No theorems found to prove in theory '${job.theoryName}'.`
                : `Completed proving theory '${job.theoryName}': ${provedCount}/${total} theorems proved (${unprovedCount} unproved) in ${elapsedMs}ms.`;
        }

        return {
            job_id: job.jobId,
            status: job.status,
            initiated_by: job.initiatedBy,
            already_running: extra?.alreadyRunning || undefined,
            file: job.filePath,
            theory: job.theoryName,
            options: job.options,
            total,
            completed,
            proved: provedCount,
            unproved: unprovedCount,
            current_formula: isRunning ? job.currentFormula : undefined,
            elapsed_ms: elapsedMs,
            theorems,
            error: job.error || undefined,
            recommended_poll_interval_seconds: isRunning ? recommendedPollSeconds : undefined,
            next_steps: isRunning
                ? `Theory proof is still running and can take several minutes. Either schedule a timer for ~${recommendedPollSeconds} seconds and then call 'get_prove_theory_status' with job_id '${job.jobId}', or call 'get_prove_theory_status' with wait_ms (e.g., 10000) to poll until status is 'completed'.`
                : undefined,
            result: resultMessage
        };
    }

    private resolveProveItBinaryAndEnv(): { proveitPath: string; env: NodeJS.ProcessEnv; defaultCwd: string } {
        const pathsInfo = this.eventsDispatcher.getPvsLibraryPathsInfo({ includeSubfolders: false });
        const pvsPath = pathsInfo.pvs_path ? fsUtils.tildeExpansion(pathsInfo.pvs_path) : "";
        let proveitPath = "proveit";

        if (pvsPath) {
            const candidate = path.join(pvsPath, "proveit");
            if (!fs.existsSync(candidate)) {
                throw new Error(`proveit binary not found at '${candidate}'. Please verify your 'pvs.path' setting ('${pvsPath}').`);
            }
            proveitPath = candidate;
        }

        const libPaths: string[] = [];
        for (const entry of pathsInfo.pvs_library_paths || []) {
            if (entry?.path && !libPaths.includes(entry.path)) {
                libPaths.push(entry.path);
            }
        }
        if (pathsInfo.nasalib?.path && pathsInfo.nasalib.exists && !libPaths.includes(pathsInfo.nasalib.path)) {
            libPaths.push(pathsInfo.nasalib.path);
        }
        if (process.env.PVS_LIBRARY_PATH) {
            for (const p of process.env.PVS_LIBRARY_PATH.split(path.delimiter)) {
                const trimmed = p.trim();
                if (trimmed && !libPaths.includes(trimmed)) {
                    libPaths.push(trimmed);
                }
            }
        }

        const currentPath = process.env.PATH || "";
        const updatedPath = pvsPath
            ? `${pvsPath}${currentPath ? path.delimiter + currentPath : ""}`
            : currentPath;

        const env: NodeJS.ProcessEnv = {
            ...process.env,
            PATH: updatedPath,
            LC_ALL: "C",
            LANG: "C"
        };
        if (libPaths.length > 0) {
            env.PVS_LIBRARY_PATH = libPaths.join(path.delimiter);
        }

        const defaultCwd = pathsInfo.workspace_path && fs.existsSync(pathsInfo.workspace_path)
            ? pathsInfo.workspace_path
            : process.cwd();

        return { proveitPath, env, defaultCwd };
    }

    private async saveDirtyPvsDocuments(): Promise<void> {
        try {
            const dirtyDocs = vscode.workspace.textDocuments.filter(
                doc => doc.isDirty && !doc.isUntitled && doc.fileName.endsWith(".pvs")
            );
            for (const doc of dirtyDocs) {
                await doc.save();
            }
        } catch (err) {
            console.warn("[mcp-http-server] Warning while saving dirty PVS documents before proveit:", err);
        }
    }

    private resolveProveItTargetAndArgs(params: {
        target: string;
        theories?: string[];
        formulas?: string[];
        all?: boolean;
        importchain?: boolean;
        clean?: boolean;
        typecheck_only?: boolean;
        timeout_secs?: number;
        force?: boolean;
        scripts?: boolean;
        write_scripts?: boolean;
        auto_fix?: number;
        log?: boolean;
        traces?: boolean;
        quiet?: boolean;
        summary_mode?: "md" | "csv";
        out?: string;
        dir?: string;
        top?: string;
        prelude_ext?: string[];
        disable_oracles?: boolean;
        disable_oracles_list?: string[];
        enable_oracles?: string[];
        default_script?: string;
        extra_args?: string[];
        defaultCwd: string;
    }): { args: string[]; resolvedTargetArg: string; cwd: string } {
        const rawTarget = (params.target || "").trim();
        if (!rawTarget) {
            throw new Error("Missing 'target' parameter for prove_with_proveit.");
        }

        const theories = (params.theories || []).map(t => t.trim()).filter(Boolean);
        const formulas = (params.formulas || []).map(f => f.trim()).filter(Boolean);

        let cwd = params.defaultCwd;
        let resolvedTargetArg = rawTarget;

        // Check if rawTarget is already a proveit @ selector: [<ctxt>]@<thf1>,..,<thfn>
        const atIndex = rawTarget.indexOf("@");
        if (atIndex !== -1) {
            const ctxtPart = rawTarget.substring(0, atIndex).trim();
            const thfPart = rawTarget.substring(atIndex + 1).trim();
            if (!thfPart) {
                throw new Error(`Invalid proveit selector '${rawTarget}': missing theory/formula specification after '@'.`);
            }
            if (ctxtPart) {
                const expandedCtxt = fsUtils.tildeExpansion(ctxtPart);
                const resolvedCtxt = path.isAbsolute(expandedCtxt) ? expandedCtxt : path.resolve(params.defaultCwd, expandedCtxt);
                if (!fs.existsSync(resolvedCtxt)) {
                    throw new Error(`Context directory not found for proveit selector: ${resolvedCtxt}`);
                }
                cwd = resolvedCtxt;
            }
            resolvedTargetArg = `@${thfPart}`;
        } else {
            // Support optional file.pvs#theory or file.pvs#theory.formula convenience format
            let pathPart = rawTarget;
            let hashSelector: string | undefined;
            if (rawTarget.includes("#")) {
                const parts = rawTarget.split("#");
                pathPart = parts[0].trim();
                hashSelector = parts[1]?.trim();
            }

            const expandedPath = fsUtils.tildeExpansion(pathPart);
            const candidatePath = path.isAbsolute(expandedPath)
                ? expandedPath
                : path.resolve(params.defaultCwd, expandedPath);

            const CandidateWithPvs = !fs.existsSync(candidatePath) && !candidatePath.endsWith(".pvs") && fs.existsSync(`${candidatePath}.pvs`)
                ? `${candidatePath}.pvs`
                : candidatePath;

            if (!fs.existsSync(CandidateWithPvs)) {
                throw new Error(`Target file or directory not found: ${candidatePath}`);
            }

            const stat = fs.statSync(CandidateWithPvs);
            if (stat.isDirectory()) {
                cwd = CandidateWithPvs;
                if (theories.length > 0 || hashSelector) {
                    const effectiveTheories = theories.length > 0 ? theories : [hashSelector!];
                    const selectorItems = effectiveTheories.map(th =>
                        formulas.length > 0 && !th.includes(".") ? `${th}.${formulas.join(":")}` : th
                    );
                    resolvedTargetArg = `@${selectorItems.join(",")}`;
                } else {
                    resolvedTargetArg = ".";
                }
            } else {
                cwd = path.dirname(CandidateWithPvs);
                const baseFileName = path.basename(CandidateWithPvs);
                const inferredTheoryFromFile = fsUtils.getFileName(CandidateWithPvs);

                if (theories.length > 0 || formulas.length > 0 || hashSelector) {
                    let effectiveTheories = theories.slice();
                    if (effectiveTheories.length === 0) {
                        if (hashSelector) {
                            effectiveTheories = [hashSelector];
                        } else {
                            // Infer theory name from file
                            const resolvedPvs = this.resolvePvsTarget(CandidateWithPvs, { mustExist: true });
                            effectiveTheories = [resolvedPvs.theoryName || inferredTheoryFromFile];
                        }
                    }
                    const selectorItems = effectiveTheories.map(th =>
                        formulas.length > 0 && !th.includes(".") ? `${th}.${formulas.join(":")}` : th
                    );
                    resolvedTargetArg = `@${selectorItems.join(",")}`;
                } else {
                    resolvedTargetArg = baseFileName;
                }
            }
        }

        const args: string[] = [];
        if (params.all) {
            args.push("-a");
        }
        if (params.clean) {
            args.push("-c");
        }
        if (params.importchain === true) {
            args.push("-i");
        } else if (params.importchain === false) {
            args.push("~i");
        }
        if (params.typecheck_only) {
            args.push("-T");
        }
        if (typeof params.timeout_secs === "number" && params.timeout_secs > 0) {
            args.push("--timeout", String(Math.floor(params.timeout_secs)));
        }
        if (params.force === false) {
            args.push("~f");
        } else if (params.force === true) {
            args.push("-f");
        }
        if (params.scripts === false) {
            args.push("~s");
        } else if (params.scripts === true) {
            args.push("-s");
        }
        if (params.write_scripts) {
            args.push("-w");
        }
        if (typeof params.auto_fix === "number" && params.auto_fix >= 0) {
            args.push("--auto-fix", String(Math.floor(params.auto_fix)));
        }
        if (params.log === true) {
            args.push("-l");
        } else if (params.log === false) {
            args.push("~l");
        }
        if (params.traces === true) {
            args.push("--traces");
        } else if (params.traces === false) {
            args.push("--no-traces");
        }
        if (params.quiet) {
            args.push("-q");
        }
        if (params.summary_mode === "md" || params.summary_mode === "csv") {
            args.push("--summary-mode", params.summary_mode);
        }
        if (params.out) {
            args.push("-o", params.out);
        }
        if (params.dir) {
            args.push("-d", fsUtils.tildeExpansion(params.dir));
        }
        if (params.top) {
            args.push("-t", params.top);
        }
        if (params.prelude_ext && params.prelude_ext.length > 0) {
            args.push("-p", params.prelude_ext.join(","));
        }
        if (params.disable_oracles) {
            args.push("--disable-oracles");
        }
        if (params.disable_oracles_list && params.disable_oracles_list.length > 0) {
            args.push("--disable", params.disable_oracles_list.join(","));
        }
        if (params.enable_oracles && params.enable_oracles.length > 0) {
            args.push("--enable", params.enable_oracles.join(","));
        }
        if (params.default_script) {
            args.push("--default-script", params.default_script);
        }
        if (params.extra_args && params.extra_args.length > 0) {
            for (const extra of params.extra_args) {
                if (typeof extra === "string" && extra.trim()) {
                    args.push(extra.trim());
                }
            }
        }

        args.push(resolvedTargetArg);
        return { args, resolvedTargetArg, cwd };
    }

    private parseProveItOutput(stdout: string, cwd: string): {
        formulas: ProveItFormulaResult[];
        grandTotals?: ProveItGrandTotals;
        summaryFiles: string[];
    } {
        const formulas: ProveItFormulaResult[] = [];
        const formulaLineRegex = /^\s*([A-Za-z0-9_?$!+-]+(?:\.[A-Za-z0-9_?$!+-]+)?)\.{3,}(proved\s*-\s*complete|proved\s*-\s*incomplete|unfinished|untried|unchecked|proved)\b(.*)$/gm;
        let match: RegExpExecArray | null;
        while ((match = formulaLineRegex.exec(stdout)) !== null) {
            const formula = match[1].trim();
            const rawStatus = match[2].replace(/\s+/g, " ").trim();
            const details = (match[3] || "").trim();
            const normalizedStatus = rawStatus.startsWith("proved") ? "proved" : rawStatus;
            formulas.push({
                formula,
                status: normalizedStatus,
                rawStatus,
                details: details || undefined
            });
        }

        let grandTotals: ProveItGrandTotals | undefined;
        const grandTotalsRegex = /Grand Totals:\s*(\d+)\s*proofs?,\s*(\d+)\s*attempted,\s*(\d+)\s*succeeded(?:.*?(\d+)\s*unfinished)?(?:.*?(\d+)\s*untried)?[^\r\n]*/gi;
        let gtMatch: RegExpExecArray | null;
        while ((gtMatch = grandTotalsRegex.exec(stdout)) !== null) {
            const totalFormulas = parseInt(gtMatch[1], 10);
            const attempted = parseInt(gtMatch[2], 10);
            const succeeded = parseInt(gtMatch[3], 10);
            const unfinished = gtMatch[4] !== undefined ? parseInt(gtMatch[4], 10) : Math.max(0, attempted - succeeded);
            const untried = gtMatch[5] !== undefined ? parseInt(gtMatch[5], 10) : Math.max(0, totalFormulas - attempted);
            grandTotals = {
                totalFormulas,
                attempted,
                succeeded,
                unfinished,
                untried,
                rawLine: gtMatch[0].trim()
            };
        }

        const summaryFiles: string[] = [];
        const summaryRegex = /([^\s"']+\.summary)\b/g;
        let sumMatch: RegExpExecArray | null;
        while ((sumMatch = summaryRegex.exec(stdout)) !== null) {
            const rawSum = sumMatch[1];
            const resolvedSum = path.isAbsolute(rawSum) ? rawSum : path.join(cwd, rawSum);
            if (!summaryFiles.includes(resolvedSum)) {
                summaryFiles.push(resolvedSum);
            }
        }

        return { formulas, grandTotals, summaryFiles };
    }

    private async waitForProveItJobOrTimeout(job: ProveItJobState, timeoutMs: number): Promise<void> {
        if (timeoutMs <= 0 || !job.completionPromise) {
            return;
        }
        if (job.status === "completed" || job.status === "cancelled" || job.status === "failed") {
            return;
        }
        await Promise.race([
            job.completionPromise,
            new Promise<void>(resolve => setTimeout(resolve, timeoutMs))
        ]);
    }

    private cancelProveItJob(job: ProveItJobState, reason: string = "Cancelled by MCP request"): void {
        if (job.status !== "running") {
            return;
        }
        job.status = "cancelled";
        job.updatedAt = Date.now();
        job.completedAt = Date.now();
        job.error = reason;

        const proc = job.process;
        if (proc && proc.pid) {
            try {
                if (process.platform !== "win32") {
                    process.kill(-proc.pid, "SIGTERM");
                } else {
                    proc.kill("SIGTERM");
                }
            } catch {
                try {
                    proc.kill("SIGTERM");
                } catch {
                    // ignore if already exited
                }
            }
        }

        if (this.currentProveItJob?.jobId === job.jobId) {
            this.currentProveItJob = null;
        }
        if (job.resolveCompletion) {
            job.resolveCompletion();
            job.resolveCompletion = undefined;
        }

        this.eventsDispatcher.getLogger()?.logEvent({
            actor: "mcp",
            source: "mcpHttpServer",
            event: "mcp.proveit.cancelled",
            action: "cancel",
            message: `Cancelled proveit job ${job.jobId}: ${reason}`,
            data: {
                jobId: job.jobId,
                status: "cancelled",
                target: job.target,
                commandLine: job.commandLine
            }
        });
    }

    private formatProveItJobPayload(job: ProveItJobState, extra?: { alreadyRunning?: boolean; tailLines?: number }) {
        const now = Date.now();
        const endTimestamp = job.completedAt || now;
        const elapsedMs = Math.max(0, endTimestamp - job.startedAt);
        const tailLines = Math.max(1, extra?.tailLines ?? 80);

        const parsed = this.parseProveItOutput(job.stdout, job.cwd);
        job.formulas = parsed.formulas;
        job.grandTotals = parsed.grandTotals;
        job.summaryFiles = parsed.summaryFiles;

        const formulas = job.formulas || [];
        const provedCount = job.grandTotals
            ? job.grandTotals.succeeded
            : formulas.filter(f => f.status === "proved").length;
        const totalCount = job.grandTotals
            ? job.grandTotals.totalFormulas
            : formulas.length;
        const unprovedCount = Math.max(0, totalCount - provedCount);
        const isRunning = job.status === "running";
        const recommendedPollSeconds = 10;

        const stdoutLines = job.stdout ? job.stdout.split(/\r?\n/) : [];
        const stderrLines = job.stderr ? job.stderr.split(/\r?\n/) : [];
        const stdoutTail = stdoutLines.slice(-tailLines).join("\n");
        const stderrTail = stderrLines.slice(-tailLines).join("\n");

        let resultMessage: string;
        if (isRunning) {
            resultMessage = extra?.alreadyRunning
                ? `A proveit batch job (${job.jobId}) is already running for '${job.target}' (${formulas.length} formulas reported so far, elapsed ${elapsedMs}ms).`
                : `Running proveit in background (job_id: '${job.jobId}') for '${job.target}' (${formulas.length} formulas reported so far, elapsed ${elapsedMs}ms).`;
        } else if (job.status === "cancelled") {
            resultMessage = `proveit job '${job.jobId}' for '${job.target}' was cancelled after ${elapsedMs}ms (${provedCount}/${totalCount} proved).`;
        } else if (job.status === "failed") {
            resultMessage = `proveit job '${job.jobId}' for '${job.target}' failed (exit code: ${job.exitCode ?? "unknown"}) after ${elapsedMs}ms: ${job.error || stderrTail || "See stdout_tail / stderr_tail for details."}`;
        } else {
            resultMessage = job.grandTotals
                ? `proveit completed for '${job.target}' in ${elapsedMs}ms: ${job.grandTotals.rawLine}`
                : `proveit completed for '${job.target}' in ${elapsedMs}ms (${provedCount}/${totalCount} formulas proved).`;
        }

        return {
            job_id: job.jobId,
            status: job.status,
            already_running: extra?.alreadyRunning || undefined,
            target: job.target,
            resolved_target_arg: job.resolvedTargetArg,
            cwd: job.cwd,
            proveit_path: job.proveitPath,
            command_line: job.commandLine,
            options: job.options,
            exit_code: job.exitCode,
            signal: job.signal,
            elapsed_ms: elapsedMs,
            grand_totals: job.grandTotals,
            total_formulas: totalCount,
            proved_formulas: provedCount,
            unproved_formulas: unprovedCount,
            formulas,
            summary_files: job.summaryFiles.length > 0 ? job.summaryFiles : undefined,
            stdout_tail: stdoutTail,
            stderr_tail: stderrTail || undefined,
            error: job.error || undefined,
            recommended_poll_interval_seconds: isRunning ? recommendedPollSeconds : undefined,
            next_steps: isRunning
                ? `proveit batch job is still running. Call 'get_proveit_status' with job_id '${job.jobId}' (optionally with wait_ms, e.g., 10000) to wait for or poll progress, or pass cancel=true to terminate the batch job.`
                : undefined,
            result: resultMessage
        };
    }

    private readDocumentationFile(topic: string): { filename: string; content: string } {
        const sanitizedTopic = path.basename(topic).toUpperCase();
        if (!ALLOWED_DOC_TOPICS.includes(sanitizedTopic as typeof ALLOWED_DOC_TOPICS[number])) {
            throw new Error(`Invalid topic. Allowed topics: ${ALLOWED_DOC_TOPICS.join(", ")}`);
        }

        const filename = `${sanitizedTopic}.md`;
        const extension = vscode.extensions.getExtension("paolomasci.vscode-pvs8");
        const workspaceFolders = vscode.workspace.workspaceFolders;
        const workspacePath = workspaceFolders && workspaceFolders.length > 0 ? workspaceFolders[0].uri.fsPath : "";

        const candidatePaths = [
            extension ? path.join(extension.extensionPath, "docs", filename) : "",
            workspacePath ? path.join(workspacePath, "docs", filename) : "",
            path.join(__dirname, "..", "..", "docs", filename)
        ].filter(Boolean);

        for (const docPath of candidatePaths) {
            if (fs.existsSync(docPath)) {
                return { filename, content: fs.readFileSync(docPath, 'utf8') };
            }
        }

        return { filename, content: `Error: ${filename} not found.` };
    }

    private createMcpServer(): McpServer {
        const mcpServer = new McpServer(
            {
                name: "vscode-pvs",
                version: "0.0.1"
            },
            {
                instructions: PVS_MCP_INSTRUCTIONS
            }
        );

        const originalRegisterTool = mcpServer.registerTool.bind(mcpServer);
        (mcpServer as any).registerTool = (name: string, config: any, cb: (...args: any[]) => Promise<any>) => {
            return originalRegisterTool(name, config, async (args: any, extra: any) => {
                const startTime = Date.now();
                const logger = this.eventsDispatcher.getLogger();
                logger?.logEvent({
                    actor: "mcp",
                    source: "mcpHttpServer",
                    event: "mcp.tool.call",
                    action: name,
                    data: args
                });
                try {
                    const result = await this.eventsDispatcher.runWithMcpContext(() => cb(args, extra));
                    let parsedResponse: any = result;
                    const firstText = result?.content?.[0]?.text;
                    if (typeof firstText === "string") {
                        try {
                            parsedResponse = JSON.parse(firstText);
                        } catch {
                            parsedResponse = firstText;
                        }
                    }
                    logger?.logEvent({
                        actor: "mcp",
                        source: "mcpHttpServer",
                        event: "mcp.tool.result",
                        action: name,
                        data: {
                            durationMs: Date.now() - startTime,
                            args,
                            response: parsedResponse
                        }
                    });
                    return result;
                } catch (err: any) {
                    logger?.logEvent({
                        actor: "mcp",
                        source: "mcpHttpServer",
                        event: "mcp.tool.error",
                        action: name,
                        level: "error",
                        message: err?.message || String(err),
                        data: {
                            durationMs: Date.now() - startTime,
                            args,
                            error: err instanceof Error ? { name: err.name, message: err.message, stack: err.stack } : String(err)
                        }
                    });
                    throw err;
                }
            });
        };

        mcpServer.registerTool(
            "start_proof",
            {
                description:
                    "Start a new proof session for a formula. Note: In this human-in-the-loop environment, if a proof session " +
                    "is already open in VS Code and you are asked to continue it, do NOT call start_proof; instead call " +
                    "apply_proof_command with '(skip)' first to inspect the current sequent.",
                inputSchema: z.object({
                    formula_path: z.string().describe("The formula path, in the format 'filepath#formula_name'")
                })
            },
            async ({ formula_path }) => {
                const resolved = this.resolvePvsTarget(formula_path, {
                    requireFormula: true,
                    mustExist: true
                });
                const formulaName = resolved.formulaName!;

                vscodeUtils.showStatusBarMessage(`[MCP] Starting proof for '${formulaName}'...`);

                const formulaRequest: ActiveFormulaSession = {
                    contextFolder: resolved.contextFolder,
                    fileName: resolved.fileName,
                    fileExtension: resolved.fileExtension,
                    theoryName: resolved.theoryName,
                    formulaName,
                    proofFile: {
                        contextFolder: resolved.contextFolder,
                        fileName: resolved.fileName,
                        fileExtension: ".jprf"
                    }
                };

                this.activeFormula = formulaRequest;

                const responsePromise = this.eventsDispatcher.waitForResponse<ProveFormulaResponse>(
                    "proveFormulaResponse",
                    {
                        timeoutMs: 60000,
                        abortOnFailToStartProof: true
                    }
                );

                // Suppress unhandled rejection if executeCommand fails or returns false before awaiting responsePromise
                responsePromise.catch(() => {});

                const started = await vscode.commands.executeCommand<boolean>(
                    "vscode-pvs.prove-formula",
                    formulaRequest
                );

                if (started === false) {
                    this.activeFormula = null;
                    throw new Error(
                        `Could not start proof for '${formulaName}' in theory '${resolved.theoryName}' (cancelled by user or failed to initialize prover).`
                    );
                }

                const desc = await responsePromise;

                let proof_id = "";
                if (desc && desc.res && typeof desc.res !== 'string') {
                    proof_id = desc.res.id || "";
                }
                if (this.activeFormula) {
                    this.activeFormula.id = proof_id;
                }

                const responsePayload = {
                    id: desc?.req?.formulaName || formulaName,
                    result: [
                        {
                            id: proof_id,
                            commentary: desc?.res && typeof desc.res !== 'string'
                                ? (typeof desc.res.commentary === 'string' ? [desc.res.commentary] : desc.res.commentary)
                                : ["Proof started"]
                        }
                    ]
                };

                return {
                    content: [{ type: "text", text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "apply_proof_command",
            {
                description:
                    "Apply a PVS proof command in the active prover session. Because a human user may also execute or undo " +
                    "steps in the VS Code UI, always send '(skip)' first when continuing an ongoing proof to poll the current " +
                    "sequent state without modifying the proof tree.",
                inputSchema: z.object({
                    command: z.string().describe("The proof command to execute (e.g., '(skip)' to poll current state, or '(grind)')")
                })
            },
            async ({ command }) => {
                if (!command || !command.trim()) {
                    throw new Error("Missing command parameter");
                }

                const isProverActive = this.eventsDispatcher.xterm?.proverSession();
                if (!this.activeFormula && isProverActive) {
                    this.syncActiveFormulaFromTarget(this.eventsDispatcher.xterm.getTheory() as PvsFormula);
                } else if (this.activeFormula && !isProverActive) {
                    this.activeFormula = null;
                }

                if (!isProverActive && !this.activeFormula) {
                    throw new Error("No active formula. Please start a proof in VS Code or run start_proof first.");
                }

                vscodeUtils.showStatusBarMessage(`[MCP] Proof command: ${command}`);

                const currentProofId = this.activeFormula?.id || "";

                const responsePromise = this.eventsDispatcher.waitForResponse<ProofCommandResponse>(
                    "proofCommandResponse",
                    { timeoutMs: 60000 }
                );
                responsePromise.catch(() => {});

                await this.eventsDispatcher.xterm.sendTextToServer(command, false, "mcp-server");

                const desc = await responsePromise;

                let commentaryList: string[] = [];
                let statusStr = "";
                let sequentObj = null;
                let resultId = currentProofId;

                if (desc && desc.res) {
                    if (typeof desc.res === 'string') {
                        commentaryList = [desc.res];
                        statusStr = desc.res;
                    } else {
                        commentaryList = typeof desc.res.commentary === 'string'
                            ? [desc.res.commentary]
                            : (desc.res.commentary || []);
                        statusStr = desc.res.status || "";
                        sequentObj = desc.res.sequent || null;
                        resultId = desc.res.id || currentProofId;
                    }
                }

                const responsePayload = {
                    result: [
                        {
                            id: resultId,
                            commentary: commentaryList,
                            status: statusStr,
                            sequent: sequentObj
                        }
                    ]
                };

                return {
                    content: [{ type: "text", text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "typecheck_file",
            {
                description: "Typecheck a PVS file",
                inputSchema: z.object({
                    file_path: z.string().describe("The absolute path of the PVS file to typecheck (e.g., '/path/to/theory.pvs')")
                })
            },
            async ({ file_path }) => {
                const resolved = this.resolvePvsTarget(file_path, { mustExist: true });

                vscodeUtils.showStatusBarMessage(`[MCP] Typechecking file: ${path.basename(resolved.filePath)}`);

                const desc = await this.runTypecheck(resolved.filePath);

                const responsePayload = {
                    file: resolved.filePath,
                    error: desc?.response?.error || undefined,
                    result: desc?.response?.result || (desc?.response?.error ? "Typechecking failed" : "Typechecking completed")
                };

                return {
                    content: [{ type: "text", text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "discharge_tccs",
            {
                description: "Discharge all TCCs (Typecheck Correctness Conditions) for a PVS file/theory",
                inputSchema: z.object({
                    file_path: z.string().describe("The absolute path of the PVS file to discharge TCCs for (e.g., '/path/to/theory.pvs')"),
                    theory_name: z.string().optional().describe("Optional theory name. If omitted, will be inferred from the file."),
                    unproved_only: z.boolean().optional().describe("If true, only discharge unproved TCCs (default: false)"),
                    use_jprf: z.boolean().optional().describe("If true, use J-PRF proofs if available (default: false)"),
                    typecheck_first: z.boolean().optional().describe("If true, ensure the file is typechecked before discharging TCCs (default: true)")
                })
            },
            async ({ file_path, theory_name, unproved_only, use_jprf, typecheck_first }) => {
                const resolved = this.resolvePvsTarget(file_path, {
                    theoryName: theory_name,
                    mustExist: true
                });

                const { filePath, theoryName } = resolved;

                if (typecheck_first !== false) {
                    vscodeUtils.showStatusBarMessage(`[MCP] Typechecking ${path.basename(filePath)} before discharging TCCs...`);
                    const tcDesc = await this.runTypecheck(filePath);

                    if (tcDesc?.response?.error) {
                        const errPayload = {
                            file: filePath,
                            theory: theoryName,
                            success: false,
                            error: tcDesc.response.error,
                            result: "Typechecking failed before discharging TCCs"
                        };
                        return {
                            content: [{ type: "text" as const, text: JSON.stringify(errPayload) }]
                        };
                    }
                }

                vscodeUtils.showStatusBarMessage(`[MCP] Discharging TCCs for ${theoryName || path.basename(filePath)}...`);

                const resource = { path: filePath, theoryName };
                const summary = await vscode.commands.executeCommand<any>(
                    "vscode-pvs.discharge-tccs",
                    resource,
                    { force: true, unprovedOnly: !!unproved_only, useJprf: !!use_jprf }
                );

                const theorems = summary?.theorems || [];
                const provedCount = theorems.filter((t: any) => t.status === "proved").length;
                const unprovedCount = theorems.filter((t: any) => t.status !== "proved").length;
                const total = summary?.total ?? theorems.length;

                const responsePayload = {
                    file: filePath,
                    theory: theoryName,
                    total,
                    proved: provedCount,
                    unproved: unprovedCount,
                    theorems,
                    result: summary
                        ? (total === 0
                            ? `No TCCs generated for theory '${theoryName}'`
                            : `Discharged ${provedCount}/${total} TCCs for theory '${theoryName}'`)
                        : "TCC discharge completed"
                };

                return {
                    content: [{ type: "text" as const, text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "prove_theory",
            {
                description: "Prove all (or only unproved) theorems in a PVS theory. Because proving an entire theory can take several minutes, this tool waits up to wait_timeout_ms (default 5000ms). If the proof finishes within that window, it returns status 'completed' with the full summary. If still running, it returns status 'running' with a job_id and progress snapshot so you can schedule a timer or call 'get_prove_theory_status' to monitor progress.",
                inputSchema: z.object({
                    file_path: z.string().describe("The absolute path of the PVS file (e.g., '/path/to/theory.pvs' or '/path/to/theory.pvs#theory_name')"),
                    theory_name: z.string().optional().describe("Optional theory name. If omitted, will be inferred from file_path or the file content."),
                    unproved_only: z.boolean().optional().describe("If true, only run proofs for unproved theorems (default: false)"),
                    use_jprf: z.boolean().optional().describe("If true, use .jprf proof files if available instead of .prf (default: false)"),
                    typecheck_first: z.boolean().optional().describe("If true, ensure the file is typechecked before proving the theory (default: true)"),
                    wait_timeout_ms: z.number().optional().describe("Milliseconds to wait for completion before returning a running background job status (default: 5000, 0 to return immediately, max: 60000)")
                })
            },
            async ({ file_path, theory_name, unproved_only, use_jprf, typecheck_first, wait_timeout_ms }) => {
                const existingJob = this.currentProveTheoryJob;
                if (existingJob && (existingJob.status === "preparing" || existingJob.status === "running")) {
                    const activePayload = this.formatProveTheoryJobPayload(existingJob, { alreadyRunning: true });
                    return {
                        content: [{ type: "text" as const, text: JSON.stringify(activePayload) }]
                    };
                }

                const resolved = this.resolvePvsTarget(file_path, {
                    theoryName: theory_name,
                    mustExist: true
                });

                const { filePath, theoryName } = resolved;

                if (typecheck_first !== false) {
                    vscodeUtils.showStatusBarMessage(`[MCP] Typechecking ${path.basename(filePath)} before proving theory '${theoryName}'...`);
                    const tcDesc = await this.runTypecheck(filePath);

                    if (tcDesc?.response?.error) {
                        const errPayload = {
                            file: filePath,
                            theory: theoryName,
                            status: "failed",
                            success: false,
                            error: tcDesc.response.error,
                            result: `Typechecking failed before proving theory '${theoryName}'`
                        };
                        return {
                            content: [{ type: "text" as const, text: JSON.stringify(errPayload) }]
                        };
                    }
                }

                const now = Date.now();
                const jobId = `prove-theory-${now}`;
                const cancellationSource = new vscode.CancellationTokenSource();
                let resolveCompletion: (() => void) | undefined;
                const completionPromise = new Promise<void>(resolve => {
                    resolveCompletion = resolve;
                });

                const job: ProveTheoryJobState = {
                    jobId,
                    status: "preparing",
                    initiatedBy: "mcp",
                    filePath,
                    theoryName,
                    options: {
                        unprovedOnly: !!unproved_only,
                        useJprf: !!use_jprf
                    },
                    startedAt: now,
                    updatedAt: now,
                    total: 0,
                    completed: 0,
                    theorems: [],
                    cancellationSource,
                    completionPromise,
                    resolveCompletion
                };

                this.currentProveTheoryJob = job;
                this.proveTheoryJobsById.set(jobId, job);

                vscodeUtils.showStatusBarMessage(`[MCP] Proving theory '${theoryName}' in ${path.basename(filePath)}...`);

                const resource = { path: filePath, theoryName };
                // Launch vscode-pvs.prove-theory asynchronously so long runs do not block the MCP HTTP call
                void Promise.resolve(
                    this.eventsDispatcher.runWithMcpContext(() =>
                        vscode.commands.executeCommand<any>(
                            "vscode-pvs.prove-theory",
                            resource,
                            {
                                origin: "mcp-server",
                                force: true,
                                unprovedOnly: !!unproved_only,
                                useJprf: !!use_jprf,
                                cancellationToken: cancellationSource.token
                            }
                        )
                    )
                ).then((summary) => {
                    if (job.status === "preparing" || job.status === "running") {
                        job.status = cancellationSource.token.isCancellationRequested ? "cancelled" : "completed";
                    }
                    if (summary) {
                        job.total = summary.total ?? job.total;
                        job.theorems = summary.theorems ? [...summary.theorems] : job.theorems;
                        job.completed = job.theorems.length;
                    }
                    job.completedAt = job.completedAt || Date.now();
                    job.updatedAt = Date.now();
                    job.currentFormula = undefined;
                    job.resolveCompletion?.();
                }).catch((err: any) => {
                    job.status = "failed";
                    job.error = err?.message || String(err);
                    job.completedAt = job.completedAt || Date.now();
                    job.updatedAt = Date.now();
                    job.currentFormula = undefined;
                    job.resolveCompletion?.();
                });

                const waitMs = Math.min(Math.max(wait_timeout_ms ?? 5000, 0), 60000);
                await this.waitForJobOrTimeout(job, waitMs);

                const responsePayload = this.formatProveTheoryJobPayload(job);
                return {
                    content: [{ type: "text" as const, text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "get_prove_theory_status",
            {
                description: "Get the live status, formula-by-formula progress, or final summary of a running or completed 'prove_theory' job (including theory proofs started by the human in VS Code). Can optionally wait up to wait_ms or cancel an active run.",
                inputSchema: z.object({
                    job_id: z.string().optional().describe("Optional job_id returned by 'prove_theory'. If omitted, inspects the active or most recent theory proof job."),
                    wait_ms: z.number().optional().describe("Optional milliseconds to wait for the job to finish before returning status (default: 0, max: 30000)."),
                    cancel: z.boolean().optional().describe("If true and the theory proof job is currently running, cancels the proof run cleanly.")
                })
            },
            async ({ job_id, wait_ms, cancel }) => {
                const job = job_id
                    ? this.proveTheoryJobsById.get(job_id) || null
                    : this.currentProveTheoryJob;

                if (!job) {
                    const idlePayload = {
                        status: "idle",
                        job_id: job_id || undefined,
                        result: job_id
                            ? `No prove_theory job found with job_id '${job_id}'.`
                            : "No prove_theory job is currently running or recorded."
                    };
                    return {
                        content: [{ type: "text" as const, text: JSON.stringify(idlePayload) }]
                    };
                }

                const isRunning = job.status === "preparing" || job.status === "running";

                if (cancel && isRunning) {
                    vscodeUtils.showStatusBarMessage(`[MCP] Cancelling theory proof for '${job.theoryName}'...`);
                    if (job.cancellationSource) {
                        job.cancellationSource.cancel();
                    } else {
                        await vscode.commands.executeCommand("vscode-pvs.interrupt-and-quit-prover");
                        job.status = "cancelled";
                        job.completedAt = Date.now();
                        job.updatedAt = Date.now();
                        job.currentFormula = undefined;
                        job.resolveCompletion?.();
                    }
                    await this.waitForJobOrTimeout(job, 2000);
                } else if (isRunning && wait_ms && wait_ms > 0) {
                    const clampedWaitMs = Math.min(Math.max(wait_ms, 0), 30000);
                    await this.waitForJobOrTimeout(job, clampedWaitMs);
                }

                const responsePayload = this.formatProveTheoryJobPayload(job);
                return {
                    content: [{ type: "text" as const, text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "start_pvsio",
            {
                description: "Start an interactive PVSio evaluator session for a PVS file or theory",
                inputSchema: z.object({
                    file_path: z.string().describe("The absolute path of the PVS file to evaluate (e.g., '/path/to/theory.pvs' or '/path/to/theory.pvs#theory_name')"),
                    theory_name: z.string().optional().describe("Optional theory name. If omitted, will be inferred from the file.")
                })
            },
            async ({ file_path, theory_name }) => {
                const resolved = this.resolvePvsTarget(file_path, {
                    theoryName: theory_name,
                    mustExist: true
                });

                vscodeUtils.showStatusBarMessage(`[MCP] Starting PVSio evaluator for theory '${resolved.theoryName}'...`);

                const req: StartXTermEvaluatorRequest = {
                    contextFolder: resolved.contextFolder,
                    fileName: resolved.fileName,
                    fileExtension: resolved.fileExtension,
                    theoryName: resolved.theoryName,
                    fileContent: resolved.fileContent
                };

                this.activeEvaluator = req;

                const success = await this.eventsDispatcher.xterm.onStartEvaluatorRequest(req);
                if (!success) {
                    this.activeEvaluator = null;
                    throw new Error(`Failed to start PVSio evaluator for theory '${resolved.theoryName}'. Please check that the file typechecks.`);
                }

                const responsePayload = {
                    status: "started",
                    file: resolved.filePath,
                    theory: resolved.theoryName,
                    prompt: "<PVSio>"
                };

                return {
                    content: [{ type: "text", text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "send_pvsio_command",
            {
                description: "Send a command or expression to the running PVSio evaluator session and receive the result",
                inputSchema: z.object({
                    command: z.string().describe("The PVSio expression or command to evaluate (e.g., '2 + 2;', 'sqrt(4);', '(defun foo () 42)!', or 'quit')")
                })
            },
            async ({ command }) => {
                if (!command || !command.trim()) {
                    throw new Error("Missing command parameter");
                }

                const isSessionActive = this.eventsDispatcher.xterm?.evaluatorSession();
                if (!isSessionActive) {
                    this.activeEvaluator = null;
                    throw new Error("No active PVSio session. Please start PVSio in VS Code or run start_pvsio first.");
                }

                if (!this.activeEvaluator) {
                    this.activeEvaluator = this.eventsDispatcher.xterm.getTheory();
                }

                let sanitizedCommand = command.trim();
                // Ensure proper PVSio termination character:
                // ';' for PVS expression evaluation, '!' for Lisp evaluation, or 'quit' to exit
                if (!sanitizedCommand.endsWith(";") && !sanitizedCommand.endsWith("!") && sanitizedCommand !== "quit") {
                    sanitizedCommand += ";";
                }

                vscodeUtils.showStatusBarMessage(`[MCP] PVSio command: ${sanitizedCommand}`);

                const responsePromise = this.eventsDispatcher.waitForResponse<EvaluatorCommandResponse>(
                    "evaluatorCommandResponse",
                    { timeoutMs: 30000 }
                );
                responsePromise.catch(() => {});

                // Send command to server via xterm so terminal UI stays in sync
                await this.eventsDispatcher.xterm.sendTextToServer(sanitizedCommand, false, "mcp-server");

                const desc = await responsePromise;

                let pvsResult: string | null = null;
                let stdOut: string | null = null;
                let errOut: string | null = null;
                let lispResult: string | null = null;
                let tccMsg: string | null = null;
                let rawStatus = "success";

                if (desc && desc.res) {
                    if (typeof desc.res === "string") {
                        if (desc.res === "bye!") {
                            rawStatus = "terminated";
                            this.activeEvaluator = null;
                        } else {
                            rawStatus = desc.res;
                        }
                    } else {
                        pvsResult = desc.res.pvsResult ? desc.res.pvsResult.trim() : null;
                        stdOut = desc.res.stdOut ? desc.res.stdOut.trim() : null;
                        errOut = desc.res.errOut ? desc.res.errOut.trim() : null;
                        lispResult = desc.res.lispResult ? desc.res.lispResult.trim() : null;
                        tccMsg = desc.res.tccMsg ? desc.res.tccMsg.trim() : null;
                    }
                }

                const responsePayload = {
                    command: sanitizedCommand,
                    status: rawStatus,
                    pvsResult,
                    stdOut,
                    errOut,
                    lispResult,
                    tccMsg,
                    state: desc?.state || null
                };

                return {
                    content: [{ type: "text", text: JSON.stringify(responsePayload) }]
                };
            }
        );

        mcpServer.registerTool(
            "restart_pvs",
            {
                title: "Restart PVS Server",
                description: "Recover PVS when it is stuck on a proof command or unresponsive. Supports hard-rebooting the PVS server process (default) or trying a soft prover interrupt-and-quit first with automatic fallback to a hard reboot. Any in-flight proof commands or batch prove-theory jobs are immediately unblocked/cancelled.",
                inputSchema: {
                    mode: z.enum(["reboot", "interrupt_and_quit"]).optional().describe("Recovery mode: 'reboot' (default) kills and restarts the PVS server process; 'interrupt_and_quit' attempts a soft prover interrupt and quit first (waiting up to 5s) and escalates to a hard reboot if PVS remains unresponsive."),
                    clean_bin: z.boolean().optional().describe("If true, cleans temporary files (.pvscontext and pvsbin cache) in the workspace before rebooting PVS (default: false)."),
                    timeout_ms: z.number().optional().describe("Maximum time in milliseconds to wait for the rebooted PVS server to report ready (default: 30000).")
                }
            },
            async ({ mode, clean_bin, timeout_ms }) => {
                const requestedMode = mode ?? "reboot";
                const cleanBin = clean_bin === true;
                const timeoutMs = timeout_ms ?? 30000;
                let actionTaken: "reboot" | "interrupt_and_quit" | "reboot_after_interrupt_timeout" = "reboot";

                if (requestedMode === "interrupt_and_quit" && !cleanBin) {
                    const softQuitSucceeded = await new Promise<boolean>((resolve) => {
                        let settled = false;
                        const cleanup = () => {
                            settled = true;
                            clearTimeout(timer);
                            this.eventsDispatcher.removeProverEventListener(onProverEvt);
                            this.eventsDispatcher.removeServerModeUpdateListener(onModeEvt);
                        };
                        const onProverEvt = (desc: ProofEditEvent | ProofExecEvent) => {
                            if (!settled && desc?.action === "did-quit-proof") {
                                cleanup();
                                resolve(true);
                            }
                        };
                        const onModeEvt = (desc: { mode: ServerMode }) => {
                            if (!settled && desc?.mode === "lisp") {
                                cleanup();
                                resolve(true);
                            }
                        };
                        const timer = setTimeout(() => {
                            if (!settled) {
                                cleanup();
                                resolve(false);
                            }
                        }, 5000);

                        this.eventsDispatcher.addProverEventListener(onProverEvt);
                        this.eventsDispatcher.addServerModeUpdateListener(onModeEvt);
                        vscode.commands.executeCommand("vscode-pvs.interrupt-and-quit-prover");
                    });

                    if (softQuitSucceeded) {
                        this.activeFormula = null;
                        return {
                            content: [{
                                type: "text",
                                text: JSON.stringify({
                                    status: "interrupted_and_quit",
                                    action_taken: "interrupt_and_quit",
                                    mode: "lisp",
                                    clean_bin: false,
                                    message: "Successfully interrupted and quit the active prover session without rebooting PVS."
                                })
                            }]
                        };
                    }
                    actionTaken = "reboot_after_interrupt_timeout";
                }

                const versionPromise = this.eventsDispatcher.waitForResponse<PvsVersionDescriptor>("pvsVersionInfo", {
                    timeoutMs
                });

                await vscode.commands.executeCommand("vscode-pvs.reboot-pvs", {
                    force: true,
                    cleanFolder: cleanBin
                });

                const versionInfo = await versionPromise;

                return {
                    content: [{
                        type: "text",
                        text: JSON.stringify({
                            status: "restarted",
                            action_taken: actionTaken,
                            mode: "lisp",
                            clean_bin: cleanBin,
                            pvs_version: versionInfo?.["pvs-version"] || null,
                            version_info: versionInfo,
                            message: "PVS server was restarted and is ready in lisp mode."
                        })
                    }]
                };
            }
        );

        mcpServer.registerTool(
            "get_pvs_library_paths",
            {
                description:
                    "Get the filesystem paths for the PVS installation, the PVS Prelude (prelude.pvs and lib subfolders), " +
                    "NASALib (and its sub-libraries), user PVS_LIBRARY_PATH folders, and the current workspace so you can " +
                    "use grep or ripgrep to search for useful lemmas, theorems, and definitions.",
                inputSchema: z.object({
                    include_subfolders: z.boolean().optional().describe(
                        "Whether to include the list of subfolder names inside Prelude and NASALib (defaults to true)."
                    )
                })
            },
            async ({ include_subfolders }) => {
                const info = this.eventsDispatcher.getPvsLibraryPathsInfo({
                    includeSubfolders: include_subfolders ?? true
                });
                return {
                    content: [{
                        type: "text",
                        text: JSON.stringify(info)
                    }]
                };
            }
        );

        mcpServer.registerTool(
            "prove_with_proveit",
            {
                description:
                    "Run PVS's 'proveit' CLI batch prover directly in a background child process for faster, headless batch proving. " +
                    "IMPORTANT: ONLY use this tool when the user EXPLICITLY asks for batch proving, asks to run 'proveit', or asks to prove without the VS Code interface. " +
                    "For standard interactive proving or UI-integrated theory verification, use 'start_proof'/'apply_proof_command' or 'prove_theory' instead. " +
                    "If 'proveit' is still running after 'wait_ms', poll or wait using 'get_proveit_status'.",
                inputSchema: {
                    target: z.string().describe(
                        "Target to prove with proveit: a .pvs file path ('/path/to/file.pvs'), a directory path ('/path/to/dir'), " +
                        "a file#theory or file#theory.formula reference, or a proveit selector ('[<ctxt>]@<thf1>,..,<thfn>' where <thfi> is <th>[.<f1>:..:<fm>])."
                    ),
                    theories: z.array(z.string()).optional().describe(
                        "Optional list of theory names (or 'theory.f1:f2' specifications) to prove within the target file or context directory."
                    ),
                    formulas: z.array(z.string()).optional().describe(
                        "Optional list of formula names to prove within the specified theory (builds '@<th>.<f1>:..:<fm>')."
                    ),
                    all: z.boolean().optional().describe("Equivalent to proveit '-a|--all' (-ciq: clean, importchain, quiet)."),
                    importchain: z.boolean().optional().describe("Prove chain of imported theories ('-i|--importchain' when true, '~i|--no-importchain' when false)."),
                    clean: z.boolean().optional().describe("Remove .pvscontext and binary files in pvsbin before proving ('-c|--clean')."),
                    typecheck_only: z.boolean().optional().describe("Typecheck but do not prove the theory ('-T|--typecheck-only')."),
                    timeout_secs: z.number().optional().describe("Timeout in seconds for each proof ('--timeout <secs>')."),
                    force: z.boolean().optional().describe("Force proof reruns ('-f|--force' when true, '~f|--no-force' when false)."),
                    scripts: z.boolean().optional().describe("Install ProofLite scripts ('-s|--scripts' when true, '~s|--no-scripts' when false)."),
                    write_scripts: z.boolean().optional().describe("Write proofs as ProofLite scripts into separate files ('-w|--write-scripts')."),
                    auto_fix: z.number().optional().describe("Try sibling proofs on unfinished branches with maximum acceptable distance ('--auto-fix <num>')."),
                    log: z.boolean().optional().describe("Log all information generated by PVS in <outfile>.log ('-l|--log' when true, '~l|--no-log' when false)."),
                    traces: z.boolean().optional().describe("Include proof traces in log file ('--traces' when true, '--no-traces' when false)."),
                    quiet: z.boolean().optional().describe("Print only untried and unfinished proofs per theory and grand total ('-q|--quiet')."),
                    summary_mode: z.enum(["md", "csv"]).optional().describe("Alternative summary mode ('--summary-mode md|csv')."),
                    out: z.string().optional().describe("Save the proof status summary in <outfile> ('-o|--out <outfile>')."),
                    dir: z.string().optional().describe("Use <dir> as default directory of summary files ('-d|--dir <dir>')."),
                    top: z.string().optional().describe("Use <topfile>.pvs instead of top.pvs when the input is a directory ('-t|--top <topfile>')."),
                    prelude_ext: z.array(z.string()).optional().describe("Load prelude extensions p1,..,pn ('-p|--prelude-ext <p1,..,pn>')."),
                    disable_oracles: z.boolean().optional().describe("Disable any external oracle ('--disable-oracles')."),
                    disable_oracles_list: z.array(z.string()).optional().describe("Disable specific external oracles ('--disable <o1,..,on>')."),
                    enable_oracles: z.array(z.string()).optional().describe("Enable specific external oracles ('--enable <o1,..,on>')."),
                    default_script: z.string().optional().describe("Default ProofLite script to be tried on unfinished branches ('--default-script <script>')."),
                    extra_args: z.array(z.string()).optional().describe("Additional raw CLI flags to pass to proveit."),
                    wait_ms: z.number().optional().describe(
                        "Time in milliseconds to wait for proveit to finish before returning an in-progress job status (default: 5000, max: 30000; set 0 to return immediately)."
                    )
                }
            },
            async (params) => {
                if (this.currentProveItJob && this.currentProveItJob.status === "running") {
                    const payload = this.formatProveItJobPayload(this.currentProveItJob, { alreadyRunning: true });
                    return {
                        content: [{
                            type: "text",
                            text: JSON.stringify(payload)
                        }]
                    };
                }

                await this.saveDirtyPvsDocuments();

                const { proveitPath, env, defaultCwd } = this.resolveProveItBinaryAndEnv();
                const { args, resolvedTargetArg, cwd } = this.resolveProveItTargetAndArgs({
                    ...params,
                    defaultCwd
                });

                const jobId = `proveit-${Date.now()}-${Math.random().toString(36).substring(2, 7)}`;
                const commandLine = [proveitPath, ...args].join(" ");
                const now = Date.now();

                let resolveCompletion: (() => void) | undefined;
                const completionPromise = new Promise<void>((resolve) => {
                    resolveCompletion = resolve;
                });

                const job: ProveItJobState = {
                    jobId,
                    status: "running",
                    target: params.target,
                    resolvedTargetArg,
                    cwd,
                    proveitPath,
                    args,
                    commandLine,
                    options: {
                        theories: params.theories,
                        formulas: params.formulas,
                        importchain: params.importchain,
                        clean: params.clean,
                        typecheckOnly: params.typecheck_only,
                        timeoutSecs: params.timeout_secs,
                        force: params.force,
                        scripts: params.scripts,
                        writeScripts: params.write_scripts,
                        autoFix: params.auto_fix,
                        log: params.log,
                        traces: params.traces,
                        quiet: params.quiet,
                        summaryMode: params.summary_mode,
                        extraArgs: params.extra_args
                    },
                    startedAt: now,
                    updatedAt: now,
                    exitCode: null,
                    signal: null,
                    stdout: "",
                    stderr: "",
                    formulas: [],
                    summaryFiles: [],
                    completionPromise,
                    resolveCompletion
                };

                this.currentProveItJob = job;
                this.proveItJobsById.set(jobId, job);

                this.eventsDispatcher.getLogger()?.logEvent({
                    actor: "mcp",
                    source: "mcpHttpServer",
                    event: "mcp.proveit.started",
                    action: "prove_with_proveit",
                    message: `Started proveit job ${jobId}: ${commandLine}`,
                    data: {
                        jobId,
                        status: "running",
                        target: params.target,
                        resolvedTargetArg,
                        cwd,
                        proveitPath,
                        args,
                        options: job.options
                    }
                });

                try {
                    const child = spawn(proveitPath, args, {
                        cwd,
                        env,
                        detached: process.platform !== "win32",
                        stdio: ["ignore", "pipe", "pipe"]
                    });
                    job.process = child;

                    child.stdout?.on("data", (chunk: Buffer | string) => {
                        job.stdout += chunk.toString();
                        job.updatedAt = Date.now();
                    });

                    child.stderr?.on("data", (chunk: Buffer | string) => {
                        job.stderr += chunk.toString();
                        job.updatedAt = Date.now();
                    });

                    child.on("error", (err: Error) => {
                        job.updatedAt = Date.now();
                        job.completedAt = Date.now();
                        if (job.status === "running") {
                            job.status = "failed";
                            job.error = err.message;
                        }
                        if (this.currentProveItJob?.jobId === job.jobId) {
                            this.currentProveItJob = null;
                        }
                        if (job.resolveCompletion) {
                            job.resolveCompletion();
                            job.resolveCompletion = undefined;
                        }
                        this.eventsDispatcher.getLogger()?.logEvent({
                            actor: "mcp",
                            source: "mcpHttpServer",
                            event: "mcp.proveit.failed",
                            action: "prove_with_proveit",
                            message: `proveit job ${job.jobId} failed to spawn: ${err.message}`,
                            data: {
                                jobId: job.jobId,
                                status: "failed",
                                durationMs: job.completedAt - job.startedAt,
                                target: job.target,
                                error: err.message
                            }
                        });
                    });

                    child.on("close", (code: number | null, signal: NodeJS.Signals | null) => {
                        job.exitCode = code;
                        job.signal = signal;
                        job.updatedAt = Date.now();
                        job.completedAt = Date.now();

                        const parsed = this.parseProveItOutput(job.stdout, job.cwd);
                        job.formulas = parsed.formulas;
                        job.grandTotals = parsed.grandTotals;
                        job.summaryFiles = parsed.summaryFiles;

                        if (job.status === "running") {
                            if (code === 0) {
                                job.status = "completed";
                            } else {
                                job.status = "failed";
                                job.error = `proveit exited with code ${code}${signal ? ` (signal: ${signal})` : ""}`;
                            }
                        }

                        if (this.currentProveItJob?.jobId === job.jobId) {
                            this.currentProveItJob = null;
                        }
                        if (job.resolveCompletion) {
                            job.resolveCompletion();
                            job.resolveCompletion = undefined;
                        }

                        this.eventsDispatcher.getLogger()?.logEvent({
                            actor: "mcp",
                            source: "mcpHttpServer",
                            event: job.status === "completed" ? "mcp.proveit.completed" : "mcp.proveit.finished",
                            action: "prove_with_proveit",
                            message: `proveit job ${job.jobId} finished with status '${job.status}' (exitCode=${code})`,
                            data: {
                                jobId: job.jobId,
                                target: job.target,
                                status: job.status,
                                durationMs: job.completedAt - job.startedAt,
                                exitCode: code,
                                signal,
                                grandTotals: job.grandTotals,
                                totalFormulas: job.formulas.length
                            }
                        });
                    });
                } catch (err: any) {
                    job.status = "failed";
                    job.completedAt = Date.now();
                    job.updatedAt = Date.now();
                    job.error = err?.message || String(err);
                    if (this.currentProveItJob?.jobId === job.jobId) {
                        this.currentProveItJob = null;
                    }
                    if (job.resolveCompletion) {
                        job.resolveCompletion();
                        job.resolveCompletion = undefined;
                    }
                }

                const waitMs = Math.min(Math.max(0, params.wait_ms ?? 5000), 30000);
                await this.waitForProveItJobOrTimeout(job, waitMs);

                const payload = this.formatProveItJobPayload(job);
                return {
                    content: [{
                        type: "text",
                        text: JSON.stringify(payload)
                    }]
                };
            }
        );

        mcpServer.registerTool(
            "get_proveit_status",
            {
                description:
                    "Get the live progress, parsed formula results, stdout/stderr output, or final summary of a running or completed 'prove_with_proveit' batch job. " +
                    "IMPORTANT: Only use this tool in conjunction with 'prove_with_proveit' when the user requested batch proving or proving without the VS Code interface.",
                inputSchema: {
                    job_id: z.string().optional().describe("Optional job ID returned by 'prove_with_proveit'. If omitted, inspects the active or most recent proveit job."),
                    wait_ms: z.number().optional().describe("Optional time in milliseconds to wait for the proveit job to finish before returning status (default: 0, max: 30000)."),
                    cancel: z.boolean().optional().describe("If true, cancels the running proveit process group (including child PVS Lisp processes)."),
                    tail_lines: z.number().optional().describe("Number of trailing stdout/stderr lines to include in the response (default: 80).")
                }
            },
            async ({ job_id, wait_ms, cancel, tail_lines }) => {
                let job: ProveItJobState | undefined;
                if (job_id) {
                    job = this.proveItJobsById.get(job_id);
                } else if (this.currentProveItJob) {
                    job = this.currentProveItJob;
                } else if (this.proveItJobsById.size > 0) {
                    const jobs = Array.from(this.proveItJobsById.values());
                    job = jobs[jobs.length - 1];
                }

                if (!job) {
                    return {
                        content: [{
                            type: "text",
                            text: JSON.stringify({
                                status: "idle",
                                job_id: job_id || null,
                                result: job_id
                                    ? `No proveit job found with job_id '${job_id}'.`
                                    : "No proveit batch job is currently running or recorded."
                            })
                        }]
                    };
                }

                if (cancel && job.status === "running") {
                    this.cancelProveItJob(job, "Cancelled by MCP get_proveit_status(cancel=true)");
                } else if (wait_ms && wait_ms > 0 && job.status === "running") {
                    const boundedWait = Math.min(Math.max(0, wait_ms), 30000);
                    await this.waitForProveItJobOrTimeout(job, boundedWait);
                }

                const payload = this.formatProveItJobPayload(job, { tailLines: tail_lines });
                return {
                    content: [{
                        type: "text",
                        text: JSON.stringify(payload)
                    }]
                };
            }
        );

        mcpServer.registerResource(
            "user-interface-docs",
            "docs://user-interface",
            {
                title: "VSCode-PVS User Interface Documentation",
                description: "Provides layout details, features, hotkeys, and tips for the VSCode-PVS user interface."
            },
            async (uri) => {
                const { content } = this.readDocumentationFile("USER-INTERFACE");
                return {
                    contents: [{
                        uri: uri.href,
                        mimeType: "text/markdown",
                        text: content
                    }]
                };
            }
        );

        mcpServer.registerResource(
            "documentation",
            new ResourceTemplate("docs://{topic}", { list: undefined }),
            {
                title: "VSCode-PVS Documentation",
                description: "Access any of the documentation files (e.g., 'USER-INTERFACE', 'FAQ', 'TUTORIAL', 'WALKTHROUGH') to get layout, features, tutorials, hotkeys, or walkthrough info."
            },
            async (uri, { topic }) => {
                const topicStr = Array.isArray(topic) ? topic[0] : topic;
                if (!topicStr) {
                    throw new Error("Missing or invalid topic parameter");
                }

                const { content } = this.readDocumentationFile(topicStr);
                return {
                    contents: [{
                        uri: uri.href,
                        mimeType: "text/markdown",
                        text: content
                    }]
                };
            }
        );

        return mcpServer;
    }

    public start(port: number): void {
        const app = express();
        app.use(express.json());
        app.use(cors());

        app.post("/mcp", async (req, res) => {
            const mcpServer = this.createMcpServer();
            const transport = new StreamableHTTPServerTransport({
                sessionIdGenerator: undefined
            });

            res.on('close', () => {
                transport.close();
                mcpServer.close();
            });

            try {
                await mcpServer.connect(transport);
                await transport.handleRequest(req, res, req.body);
            } catch (error) {
                console.error('Error to process the request:', error);
                if (!res.headersSent) {
                    res.status(500).json({
                        jsonrpc: '2.0',
                        error: { code: -32603, message: 'Internal MCP Error' }
                    });
                }
            }
        });

        this.server = app.listen(port, () => {
            const mcpUrl = `http://localhost:${port}/mcp`;
            console.log(`[mcp-http-server] Integration HTTP server listening on port ${port}`);
            console.log(`[mcp-http-server] Started MCP on: ${mcpUrl}`);
            this.eventsDispatcher.getLogger()?.logEvent({
                actor: "system",
                source: "mcpHttpServer",
                event: "mcp.server.started",
                action: "start",
                message: `Started MCP on: ${mcpUrl}`,
                data: { port, mcpUrl }
            });
            vscode.window.showInformationMessage(`Started MCP on: ${mcpUrl}`);
        });
    }

    public stop(): void {
        if (this.currentProveItJob && this.currentProveItJob.status === "running") {
            this.cancelProveItJob(this.currentProveItJob, "MCP HTTP server stopped");
        }
        this.unregisterSessionSyncListeners();
        if (this.server) {
            this.server.close();
            this.server = null;
            console.log(`[mcp-http-server] Integration HTTP server stopped.`);
            this.eventsDispatcher.getLogger()?.logEvent({
                actor: "system",
                source: "mcpHttpServer",
                event: "mcp.server.stopped",
                action: "stop",
                message: "Integration HTTP server stopped."
            });
        }
    }
}
