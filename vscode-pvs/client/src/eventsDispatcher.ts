/**
 * @module VSCodeEventsDispatcher
 * @author Paolo Masci
 * @date 2019.10.12
 * @copyright
 * Copyright 2019 United States Government as represented by the Administrator
 * of the National Aeronautics and Space Administration. All Rights Reserved.
 *
 * Disclaimers
 *
 * No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY
 * WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY,
 * INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE
 * WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM
 * INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR
 * FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO
 * THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER,
 * CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT
 * OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY
 * OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.
 * FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES
 * REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE,
 * AND DISTRIBUTES IT "AS IS."
 *
 * Waiver and Indemnity: RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS
 * AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND
 * SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF
 * THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES,
 * EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM
 * PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT
 * SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED
 * STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY
 * PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE
 * REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL
 * TERMINATION OF THIS AGREEMENT.
 **/

import { CancellationToken, LanguageClient } from "vscode-languageclient";
import { VSCodePvsStatusBar } from "./views/vscodePvsStatusBar";
import { VSCodePvsEmacsBindingsProvider } from "./providers/vscodePvsEmacsBindingsProvider";
import { VSCodePvsWorkspaceExplorer, TheoryItem, TccsOverviewItem, WorkspaceOverviewItem, FormulaItem, ProveTheoryProgressEvent } from "./views/vscodePvsWorkspaceExplorer";
import { VSCodePvsProofExplorer, ProofItem, ProofExplorerEvent } from "./views/vscodePvsProofExplorer";
// import { TerminalSession, VSCodePvsTerminal } from "./views/vscodePvsTerminal";
import {
    PvsContextDescriptor, serverEvent, serverRequest, PvsVersionDescriptor,
    ProofDescriptor, ServerMode, PvsFormula, ProofEditEvent, PvsProofCommand,
    ProofExecEvent, PvsTheory, ProofExecInterruptProver, WorkspaceEvent,
    ProofExecInterruptAndQuitProver, FileDescriptor, ContextFolder,
    PvsioEvaluatorCommand, EvalExpressionRequest, ProveFormulaResponse,
    ProofCommandResponse, ProofMateProfile, ProveFormulaRequest, PvsFile,
    EvaluatorCommandResponse,
    CopyProofliteRequest, SaveProofResponse, GotoFileDescriptor,
    FormulaDescriptor, quickFixReplaceCommand, QuickFixReplace, QuickFixAddImporting,
    quickFixAddImportingCommand, VSCodePvsVersionDescriptor, DumpPvsFilesRequest,
    DumpPvsFilesResponse, UndumpPvsFilesRequest, UndumpPvsFilesResponse, FollowLink,
    TypeCheckFileRequest,
    PrettyPrintExpandedResponse
} from "./common/serverInterface";
import { window, commands, ExtensionContext, ProgressLocation, Selection, Uri, workspace } from "vscode";
import * as vscode from 'vscode';
import { PvsResponse } from "./common/pvs-gui";
import * as fsUtils from './common/fsUtils';
import { VSCodePvsProofMate } from "./views/vscodePvsProofMate";
import * as utils from './common/languageUtils';
import * as vscodeUtils from './utils/vscode-utils';
import { PvsLogActor, PvsLogEntry, VSCodePvsLogger } from "./views/vscodePvsLogger";
import { VSCodePvsPackageManager } from "./providers/vscodePvsPackageManager";
import { VSCodePvsPlotter } from "./views/vscodePvsPlotter";
import { VSCodePvsSearch } from "./views/vscodePvsSearch";
import { VSCodePvsioWeb } from "./views/vscodePvsioWeb";
import { StartXTermEvaluatorRequest, VSCodePvsXTerm } from "./views/vscodePvsXTerm";
import { colorText, PvsColor } from "./common/colorUtils";
import { YesNoCancel, quickFixReplace, quickFixAddImporting, RunningTask, showWarningMessage } from "./utils/vscode-utils";
import { findTheoryName, getUndumpFolderName, isDumpFile, isPvsFile } from "./common/fsUtils";
import { VSCodePvsFileViewer } from "./views/vscodePvsFileViewer";

import * as fs from 'fs';
import * as path from 'path';
import { log } from "console";
import { VSCodePvsPathEvaluator } from "./views/vscodePvsPathEvaluator";

// FIXME: use Backbone.Model
export class EventsDispatcher {
    public client: LanguageClient;
    protected statusBar: VSCodePvsStatusBar;
    protected emacsBindings: VSCodePvsEmacsBindingsProvider;
    public workspaceExplorer: VSCodePvsWorkspaceExplorer;
    protected proofExplorer: VSCodePvsProofExplorer;

    // protected vscodePvsTerminal: VSCodePvsTerminal;
    public xterm: VSCodePvsXTerm;

    // debounce timer
    protected uiDebouncer: NodeJS.Timeout = null;

    protected proofMate: VSCodePvsProofMate;
    protected logger: VSCodePvsLogger;
    protected packageManager: VSCodePvsPackageManager;
    protected plotter: VSCodePvsPlotter;
    protected search: VSCodePvsSearch;
    protected pvsIoWeb: VSCodePvsioWeb;
    protected fileViewer: VSCodePvsFileViewer;

    protected inChecker: boolean = false;
    protected inEvaluator: boolean = false;
    protected quietMode: boolean = false;
    protected showTheoriesFromActiveFile: boolean = true;

    protected NOTIFICATION_TIMEOUT: number = 2000; // 2sec

    protected pvsFailureHandlers: Array<(params: any) => void> = [];
    protected pathEvaluator: VSCodePvsPathEvaluator;

    protected responseListeners: Map<string, Set<(desc: any) => void>> = new Map();
    protected activeMcpDepth: number = 0;

    public getLogger(): VSCodePvsLogger {
        return this.logger;
    }

    public async runWithMcpContext<T>(fn: () => PromiseLike<T> | T): Promise<T> {
        this.activeMcpDepth++;
        try {
            return await fn();
        } finally {
            this.activeMcpDepth = Math.max(0, this.activeMcpDepth - 1);
        }
    }

    public getCurrentActor(hint?: any): PvsLogActor {
        if (
            hint?.origin === "mcp-server" ||
            hint?.initiatedBy === "mcp" ||
            this.activeMcpDepth > 0
        ) {
            return "mcp";
        }
        return "user";
    }

    protected sanitizeLogValue(val: any, depth: number = 0): any {
        if (val === null || val === undefined) {
            return val;
        }
        if (typeof val === "string") {
            return val.length > 4000 ? val.substring(0, 4000) + "...[truncated]" : val;
        }
        if (typeof val === "number" || typeof val === "boolean") {
            return val;
        }
        if (val instanceof RegExp) {
            return val.toString();
        }
        if (depth > 3) {
            return "[Object]";
        }
        if (Array.isArray(val)) {
            return val.slice(0, 50).map(item => this.sanitizeLogValue(item, depth + 1));
        }
        if (typeof val === "object") {
            if (typeof val.fsPath === "string") {
                return { fsPath: val.fsPath, path: val.path };
            }
            const out: Record<string, any> = {};
            const skipKeys = new Set(["fileContent", "cancellationToken", "parent", "children", "context", "client"]);
            for (const key of Object.keys(val)) {
                if (skipKeys.has(key) || typeof val[key] === "function") {
                    continue;
                }
                out[key] = this.sanitizeLogValue(val[key], depth + 1);
            }
            return out;
        }
        return String(val);
    }

    protected sanitizeLogArgs(args: any[]): any {
        const sanitized = args && args.length > 0 ? this.sanitizeLogValue(args) : [];
        const activeFile = vscodeUtils.getActivePvsEditor()?.document?.fileName;
        if ((!args || args.length === 0 || args[0] === undefined) && activeFile) {
            return { args: sanitized, activeFile };
        }
        return sanitized;
    }

    protected log(message: string, meta?: Partial<PvsLogEntry>): void {
        console.log(message);
        this.logger?.logConsole(message, {
            source: "eventsDispatcher",
            ...meta,
            data: meta?.data !== undefined ? this.sanitizeLogValue(meta.data) : undefined
        });
    }

    protected logError(message: string, error?: any, meta?: Partial<PvsLogEntry>): void {
        if (error !== undefined) {
            console.error(message, error);
        } else {
            console.error(message);
        }
        this.logger?.logError(message, error, {
            source: "eventsDispatcher",
            ...meta,
            data: meta?.data !== undefined ? this.sanitizeLogValue(meta.data) : this.sanitizeLogValue(error)
        });
    }

    protected registerCommand(commandId: string, callback: (...args: any[]) => any): vscode.Disposable {
        const systemInternalCommands = new Set([
            "vscode-pvs.ready",
            "vscode-pvs.progress-info",
            "xterm.showFeedbackWhileExecuting",
            "xterm.did-execute-command",
            "xterm-pvs.focus"
        ]);
        return commands.registerCommand(commandId, async (...args: any[]) => {
            if (commandId !== "vscode-pvs.ignore-keypress") {
                const hint = (args && (args[1]?.origin || args[1]?.initiatedBy)) ? args[1] : args?.[0];
                const actor: PvsLogActor = systemInternalCommands.has(commandId)
                    ? "system"
                    : this.getCurrentActor(hint);
                this.logger?.logEvent({
                    level: "info",
                    actor,
                    source: "eventsDispatcher",
                    event: "vscode.command",
                    action: commandId,
                    data: this.sanitizeLogArgs(args)
                });
            }
            return await callback(...args);
        });
    }

    protected addResponseListener<T>(event: string, cb: (desc: T) => void): void {
        if (!this.responseListeners.has(event)) {
            this.responseListeners.set(event, new Set());
        }
        this.responseListeners.get(event).add(cb);
    }

    protected removeResponseListener<T>(event: string, cb: (desc: T) => void): void {
        this.responseListeners.get(event)?.delete(cb);
    }

    protected emitResponse<T>(event: string, data: T): void {
        const listeners = this.responseListeners.get(event);
        if (listeners) {
            Array.from(listeners).forEach(listener => {
                try {
                    listener(data);
                } catch (e) {
                    console.error(`Error in ${event} listener`, e);
                }
            });
        }
    }

    public waitForResponse<T>(
        event: "proofCommandResponse" | "proveFormulaResponse" | "typecheckFileResponse" | "dischargeTccsResponse" | "proveTheoryResponse" | "evaluatorCommandResponse" | "pvsVersionInfo",
        options?: {
            timeoutMs?: number;
            filter?: (data: T) => boolean;
            abortOnFailToStartProof?: boolean;
        }
    ): Promise<T> {
        const timeoutMs = options?.timeoutMs ?? 60000;
        const abortOnReboot = event !== "pvsVersionInfo";
        return new Promise<T>((resolve, reject) => {
            let settled = false;
            const cleanup = () => {
                settled = true;
                if (timeoutId) {
                    clearTimeout(timeoutId);
                }
                this.removeResponseListener(event, onResponse);
                this.removePvsFailureListener(onFailure);
                if (abortOnReboot) {
                    this.removeResponseListener("pvsServerRebooting", onReboot);
                }
                if (options?.abortOnFailToStartProof) {
                    this.removeProverEventListener(onProverEvent);
                }
            };

            const onResponse = (data: T) => {
                if (settled) { return; }
                if (options?.filter && !options.filter(data)) {
                    return;
                }
                cleanup();
                resolve(data);
            };

            const onFailure = (params: any) => {
                if (settled) { return; }
                cleanup();
                const errMsg = params?.msg || "PVS server failure occurred while waiting for response";
                reject(new Error(errMsg));
            };

            const onReboot = (params: { msg?: string }) => {
                if (settled) { return; }
                cleanup();
                reject(new Error(params?.msg || "PVS server was restarted while waiting for response"));
            };

            const onProverEvent = (desc: ProofEditEvent | ProofExecEvent) => {
                if (settled) { return; }
                if (desc?.action === "did-fail-to-start-proof") {
                    cleanup();
                    reject(new Error(desc.msg || "Failed to start prover session"));
                }
            };

            const timeoutId = timeoutMs > 0 ? setTimeout(() => {
                if (settled) { return; }
                cleanup();
                reject(new Error(`Timeout waiting for ${event} (${timeoutMs}ms)`));
            }, timeoutMs) : null;

            this.addResponseListener(event, onResponse);
            this.addPvsFailureListener(onFailure);
            if (abortOnReboot) {
                this.addResponseListener("pvsServerRebooting", onReboot);
            }
            if (options?.abortOnFailToStartProof) {
                this.addProverEventListener(onProverEvent);
            }
        });
    }

    public addPvsFailureListener(cb: (params: any) => void): void {
        this.pvsFailureHandlers.push(cb);
    }

    public removePvsFailureListener(cb: (params: any) => void): void {
        this.pvsFailureHandlers = this.pvsFailureHandlers.filter(l => l !== cb);
    }

    public addProverEventListener(cb: (desc: ProofEditEvent | ProofExecEvent) => void): void {
        this.addResponseListener("proverEvent", cb);
    }

    public removeProverEventListener(cb: (desc: ProofEditEvent | ProofExecEvent) => void): void {
        this.removeResponseListener("proverEvent", cb);
    }

    public addServerModeUpdateListener(cb: (desc: { mode: ServerMode }) => void): void {
        this.addResponseListener("serverModeUpdateEvent", cb);
    }

    public removeServerModeUpdateListener(cb: (desc: { mode: ServerMode }) => void): void {
        this.removeResponseListener("serverModeUpdateEvent", cb);
    }

    public addProofCommandResponseListener(cb: (desc: ProofCommandResponse) => void): void {
        this.addResponseListener("proofCommandResponse", cb);
    }

    public removeProofCommandResponseListener(cb: (desc: ProofCommandResponse) => void): void {
        this.removeResponseListener("proofCommandResponse", cb);
    }

    public addProveFormulaResponseListener(cb: (desc: ProveFormulaResponse) => void): void {
        this.addResponseListener("proveFormulaResponse", cb);
    }

    public removeProveFormulaResponseListener(cb: (desc: ProveFormulaResponse) => void): void {
        this.removeResponseListener("proveFormulaResponse", cb);
    }

    public addTypecheckFileResponseListener(cb: (desc: any) => void): void {
        this.addResponseListener("typecheckFileResponse", cb);
    }

    public removeTypecheckFileResponseListener(cb: (desc: any) => void): void {
        this.removeResponseListener("typecheckFileResponse", cb);
    }

    public addDischargeTccsResponseListener(cb: (desc: any) => void): void {
        this.addResponseListener("dischargeTccsResponse", cb);
    }

    public removeDischargeTccsResponseListener(cb: (desc: any) => void): void {
        this.removeResponseListener("dischargeTccsResponse", cb);
    }

    public addEvaluatorCommandResponseListener(cb: (desc: EvaluatorCommandResponse) => void): void {
        this.addResponseListener("evaluatorCommandResponse", cb);
    }

    public removeEvaluatorCommandResponseListener(cb: (desc: EvaluatorCommandResponse) => void): void {
        this.removeResponseListener("evaluatorCommandResponse", cb);
    }

    public addProveTheoryProgressListener(cb: (desc: ProveTheoryProgressEvent) => void): void {
        this.addResponseListener("proveTheoryProgress", cb);
    }

    public removeProveTheoryProgressListener(cb: (desc: ProveTheoryProgressEvent) => void): void {
        this.removeResponseListener("proveTheoryProgress", cb);
    }

    public addProveTheoryResponseListener(cb: (desc: { theory: PvsTheory; summary: fsUtils.TheorySummary | null; tccsOnly?: boolean; cancelled?: boolean; error?: string }) => void): void {
        this.addResponseListener("proveTheoryResponse", cb);
    }

    public removeProveTheoryResponseListener(cb: (desc: { theory: PvsTheory; summary: fsUtils.TheorySummary | null; tccsOnly?: boolean; cancelled?: boolean; error?: string }) => void): void {
        this.removeResponseListener("proveTheoryResponse", cb);
    }

    public addPvsVersionInfoListener(cb: (desc: PvsVersionDescriptor) => void): void {
        this.addResponseListener("pvsVersionInfo", cb);
    }

    public removePvsVersionInfoListener(cb: (desc: PvsVersionDescriptor) => void): void {
        this.removeResponseListener("pvsVersionInfo", cb);
    }

    public addPvsServerRebootingListener(cb: (desc: { msg?: string }) => void): void {
        this.addResponseListener("pvsServerRebooting", cb);
    }

    public removePvsServerRebootingListener(cb: (desc: { msg?: string }) => void): void {
        this.removeResponseListener("pvsServerRebooting", cb);
    }

    public getPvsLibraryPathsInfo(opt?: { includeSubfolders?: boolean }): {
        pvs_path: string;
        pvs_path_exists: boolean;
        prelude: {
            path: string | null;
            exists: boolean;
            main_file: string | null;
            main_file_exists: boolean;
            pvsio_file: string | null;
            subfolders?: string[];
        };
        nasalib: {
            path: string | null;
            exists: boolean;
            subfolders?: string[];
        };
        pvs_library_paths: { path: string; exists: boolean }[];
        workspace_path: string | null;
    } {
        const includeSubfolders = opt?.includeSubfolders ?? true;
        const rawPvsPath = vscodeUtils.getConfiguration("pvs.path")?.trim() || "";
        const pvsPath = rawPvsPath ? fsUtils.tildeExpansion(rawPvsPath) : "";
        const pvsPathExists = !!(pvsPath && fsUtils.folderExists(pvsPath));

        const preludePath = pvsPath ? path.join(pvsPath, "lib") : null;
        const preludeExists = !!(preludePath && fsUtils.folderExists(preludePath));
        const preludeMainFile = preludePath ? path.join(preludePath, "prelude.pvs") : null;
        const preludeMainFileExists = !!(preludeMainFile && fsUtils.fileExists(preludeMainFile));
        const preludePvsioFile = preludePath ? path.join(preludePath, "pvsio_prelude.pvs") : null;

        const configuredLibPaths = vscodeUtils.getPvsLibraryPaths();
        const envLibPaths = (process.env["PVS_LIBRARY_PATH"] || "")
            .split(path.delimiter)
            .map(p => p.trim())
            .filter(Boolean);
        const allLibPathsSet = new Set<string>();
        for (const p of [...configuredLibPaths, ...envLibPaths]) {
            const expanded = fsUtils.tildeExpansion(p);
            if (expanded) {
                allLibPathsSet.add(expanded);
            }
        }
        const allLibPaths = Array.from(allLibPathsSet);

        let nasalibPath: string | null =
            fsUtils.getNasalibPath(vscodeUtils.getPvsLibraryPath()) ||
            fsUtils.getNasalibPath(process.env["PVS_LIBRARY_PATH"] || "") ||
            null;

        if (!nasalibPath && pvsPath) {
            const bundledNasalib = path.join(pvsPath, "nasalib");
            if (fsUtils.folderExists(bundledNasalib)) {
                nasalibPath = bundledNasalib;
            }
        }

        if (!nasalibPath) {
            for (const candidate of allLibPaths) {
                if (!fsUtils.folderExists(candidate)) continue;
                if (path.basename(candidate.replace(/\/+$/, "")).toLowerCase() === "nasalib") {
                    nasalibPath = candidate;
                    break;
                }
                const pvsLibContent = fsUtils.readFile(path.join(candidate, ".pvslib"));
                if (pvsLibContent && /id:\s*NASALib/i.test(pvsLibContent)) {
                    nasalibPath = candidate;
                    break;
                }
            }
        }

        const nasalibExists = !!(nasalibPath && fsUtils.folderExists(nasalibPath));

        const listCleanSubfolders = (dirPath: string | null, exists: boolean): string[] | undefined => {
            if (!includeSubfolders) return undefined;
            if (!dirPath || !exists) return [];
            const folders = fsUtils.listSubFolders(dirPath) || [];
            return folders
                .filter(name => name && !name.startsWith("."))
                .sort((a, b) => a.localeCompare(b));
        };

        const workspacePath = this.workspaceExplorer?.getCurrentWorkspace() || vscodeUtils.getRootFolder() || null;

        return {
            pvs_path: pvsPath,
            pvs_path_exists: pvsPathExists,
            prelude: {
                path: preludePath,
                exists: preludeExists,
                main_file: preludeMainFile,
                main_file_exists: preludeMainFileExists,
                pvsio_file: preludePvsioFile,
                ...(includeSubfolders ? { subfolders: listCleanSubfolders(preludePath, preludeExists) } : {})
            },
            nasalib: {
                path: nasalibPath,
                exists: nasalibExists,
                ...(includeSubfolders ? { subfolders: listCleanSubfolders(nasalibPath, nasalibExists) } : {})
            },
            pvs_library_paths: allLibPaths.map(p => ({
                path: p,
                exists: fsUtils.folderExists(p)
            })),
            workspace_path: workspacePath
        };
    }

    protected async resolveActiveResource<T>(resource: T, opt?: { save?: boolean }): Promise<T | { path: string }> {
        const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
        if (activeEditor?.document) {
            if (opt?.save) {
                await activeEditor.document.save();
            }
            if (!resource) {
                return { path: activeEditor.document.fileName };
            }
        }
        return resource;
    }

    protected async executeTheoryProof(
        desc: PvsTheory,
        opt: {
            tccsOnly?: boolean;
            useJprf?: boolean;
            unprovedOnly?: boolean;
            match?: RegExp;
            progressMsg: string;
            cancellationToken?: CancellationToken;
        }
    ): Promise<fsUtils.TheorySummary | null> {
        this.quietMode = true;
        this.proofMate.disableView();
        this.proofExplorer.disableView();
        this.xterm.bye();
        this.statusBar.showProgress(opt.progressMsg);

        let lastPhase = "preparing" as ProveTheoryProgressEvent["phase"];
        let lastError: string | undefined;

        try {
            const summary = await this.workspaceExplorer.proveTheoryWithProgress(desc, {
                tccsOnly: opt.tccsOnly,
                useJprf: opt.useJprf,
                unprovedOnly: opt.unprovedOnly,
                match: opt.match,
                cancellationToken: opt.cancellationToken,
                onProgress: (evt) => {
                    lastPhase = evt.phase;
                    if (evt.error) {
                        lastError = evt.error;
                    }
                    this.logger?.logEvent({
                        level: evt.phase === "failed" ? "error" : "info",
                        actor: "server",
                        source: "eventsDispatcher",
                        event: "proveTheoryProgress",
                        action: evt.phase,
                        data: this.sanitizeLogValue(evt)
                    });
                    this.emitResponse("proveTheoryProgress", evt);
                }
            });
            const responseEventName = opt.tccsOnly ? "dischargeTccsResponse" : "proveTheoryResponse";
            const payload = {
                theory: desc,
                summary,
                tccsOnly: opt.tccsOnly,
                cancelled: lastPhase === "cancelled",
                error: lastError
            };
            this.logger?.logEvent({
                level: lastError ? "error" : "info",
                actor: "server",
                source: "eventsDispatcher",
                event: responseEventName,
                action: lastPhase,
                data: this.sanitizeLogValue(payload)
            });
            this.emitResponse(responseEventName, payload);
            return summary;
        } catch (error: any) {
            const errMsg = error?.msg || error?.message || String(error || "Unknown error during theory proof");
            const responseEventName = opt.tccsOnly ? "dischargeTccsResponse" : "proveTheoryResponse";
            const payload = {
                theory: desc,
                summary: null,
                tccsOnly: opt.tccsOnly,
                cancelled: false,
                error: errMsg
            };
            this.logger?.logEvent({
                level: "error",
                actor: "server",
                source: "eventsDispatcher",
                event: responseEventName,
                action: "failed",
                data: this.sanitizeLogValue(payload)
            });
            this.emitResponse(responseEventName, payload);
            return null;
        } finally {
            this.statusBar.clear();
            this.statusBar.ready();
            this.quietMode = false;
        }
    }

    protected async executeDischargeTccs(
        desc: PvsTheory,
        opt: { useJprf?: boolean; unprovedOnly?: boolean; match?: RegExp; progressMsg: string; cancellationToken?: CancellationToken }
    ): Promise<fsUtils.TheorySummary | null> {
        return await this.executeTheoryProof(desc, {
            ...opt,
            tccsOnly: true
        });
    }

    protected async sendActiveEditorLatexRequest(requestType: string, resource?: any): Promise<void> {
        const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
        if (activeEditor?.document) {
            await activeEditor.document.save();

            const fname: string = activeEditor.document.fileName;
            const cursorPosition: vscode.Position = activeEditor.selection?.active;
            const text: string = activeEditor.document.getText();

            const desc: FileDescriptor = vscodeUtils.resource2fileDescriptor({
                theoryName: findTheoryName(text, cursorPosition ? cursorPosition.line : 0),
                formulaName: null,
                fileName: fsUtils.getFileName(fname),
                fileExtension: fsUtils.getFileExtension(fname),
                contextFolder: fsUtils.getContextFolder(fname)
            });

            if (isPvsFile(desc)) {
                this.client.sendRequest(requestType, desc);
            } else {
                showWarningMessage(`Tried to latexify a non 'pvs' file.`);
            }
        } else {
            this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
        }
    }

    constructor (client: LanguageClient, handlers: {
        statusBar: VSCodePvsStatusBar,
        emacsBindings: VSCodePvsEmacsBindingsProvider,
        workspaceExplorer: VSCodePvsWorkspaceExplorer,
        proofExplorer: VSCodePvsProofExplorer,

        // vscodePvsTerminal: VSCodePvsTerminal,
        xterm: VSCodePvsXTerm,

        proofMate: VSCodePvsProofMate,
        logger: VSCodePvsLogger,
        packageManager: VSCodePvsPackageManager,
        plotter: VSCodePvsPlotter,
        search: VSCodePvsSearch,
        pvsioweb: VSCodePvsioWeb,
        fileViewer: VSCodePvsFileViewer,
        pathEvaluator: VSCodePvsPathEvaluator
    }) {
        this.client = client;
        this.statusBar = handlers.statusBar;
        this.emacsBindings = handlers.emacsBindings;
        this.workspaceExplorer = handlers.workspaceExplorer;
        this.proofExplorer = handlers.proofExplorer;

        this.proofExplorer.on(ProofExplorerEvent.didStopExecution, () => {
            if (!this.proofMate.isRunning()) {
                this.proofMate.pauseProof({ force: true, source: "proof-explorer" });
                setTimeout(() => {
                    this.xterm.focus(); // use a timeout so that proof-explorer does not steal the focus
                    this.xterm.showWelcomeMessage();
                }, 250);
            }
        });

        // this.vscodePvsTerminal = handlers.vscodePvsTerminal;
        this.xterm = handlers.xterm;

        this.proofMate = handlers.proofMate;
        this.logger = handlers.logger;
        this.packageManager = handlers.packageManager;
        this.plotter = handlers.plotter;
        this.search = handlers.search;
        this.pvsIoWeb = handlers.pvsioweb;
        this.fileViewer = handlers.fileViewer;
        this.pathEvaluator = handlers.pathEvaluator;
    }
	activate (context: ExtensionContext): void {
        // -- handlers for server responses
        this.client.onRequest(serverEvent.evaluatorCommandResponse, (data: EvaluatorCommandResponse) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.evaluatorCommandResponse} - param: ${JSON.stringify(data)}`,
                { actor: "server", event: serverEvent.evaluatorCommandResponse, data }
            );
            this.emitResponse("evaluatorCommandResponse", data);
        });
		this.client.onRequest(serverEvent.pvsVersionInfo, async (version: PvsVersionDescriptor) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.pvsVersionInfo} - param: ${version} `,
                { actor: "server", event: serverEvent.pvsVersionInfo, data: version }
            ); // #DEBUG
			if (version) {
                this.statusBar.pvsReady(version);
                vscode.commands.executeCommand('setContext', 'nasalib-present', !!version["nasalib-version"]);
                this.statusBar.toggleVisibilityDownloadNasalibButton(!version["nasalib-version"]);
                try {
                    // check if this is a session start and there's a file that needs to be opened
                    const currentWorkspace: string = vscodeUtils.getRootFolder();
                    const toBeOpened: string = await vscodeUtils.getFileToBeOpened(currentWorkspace);
                    const fname: string = toBeOpened || vscode?.window?.activeTextEditor?.document?.fileName;
                    // if this workspace is untitled, open a folder
                    if (!vscode.workspace.name && fname) {
                        if (!vscode.workspace.name) {
                            // 'vscode.openFolder' will cause a restart of the vscode-pvs extension
                            // any instruction after this command won't have any effect
                            // we need to write a configuration file .vscode/file.json to instruct
                            // the new vscode-pvs session to opened the file in the editor
                            const contextFolder: string = fsUtils.getContextFolder(fname);
                            if (contextFolder) {
                                await vscodeUtils.saveFileToBeOpened(contextFolder, fname);
                                await commands.executeCommand('vscode.openFolder', Uri.file(contextFolder), {
                                    // forceNewWindow: true,
                                    forceReuseWindow: true
                                });
                                return;
                            }
                            // don't update file-explorer --- any modification will create an Untitled workspace, which might be problematic for vscode-pvs users
                            // const contextFolderUri: Uri = Uri.file(contextFolder);
                            // if (!workspace.getWorkspaceFolder(contextFolderUri)) {
                            //     await vscode.commands.executeCommand("workbench.action.closeAllGroups");
                            // 	// new workspace folder: set a new root of the current workspace
                            // 	// commands.executeCommand('vscode.openFolder', Uri.file(contextFolder), { forceReuseWindow: true });
                            // 	const nOpenFolders: number = workspace?.workspaceFolders?.length || 0;
                            // 	await vscodeUtils.updateWorkspaceFolders(0, nOpenFolders, { uri: Uri.file(contextFolder) });
                            // }
                        }
                    }
                    // if the configuration file indicated there's a file to be opened, then open that file in the editor
                    if (toBeOpened) {
                        // close all open files -- these are left-overs from a previous session
                        await vscodeUtils.closeOpenEditors();
                        // open file in the editor
                        await vscodeUtils.openPvsFile(toBeOpened);
                        // highlight file in file-explorer
                        vscodeUtils.showActiveFileInExplorer();
                    }
                } catch (err) {
                    this.logError(`[event-dispatcher] Error while trying to open new workspace`, err);
                } finally {
                    this.statusBar.showVersionDialog({ trailingNote: " :: Ready! ::"});
                    this.emitResponse("pvsVersionInfo", version);
                }
			}
		});
		this.client.onRequest(serverEvent.contextUpdate, (desc: PvsContextDescriptor) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.contextUpdate} - param: ${JSON.stringify(desc)} `,
                { actor: "server", event: serverEvent.contextUpdate, data: desc }
            ); // #DEBUG
			if (this.workspaceExplorer) {
				this.workspaceExplorer.updateContextFolder(desc, { theoriesFromActiveFile: this.showTheoriesFromActiveFile });
			}
		});
		this.client.onRequest(serverEvent.latexTheoriesResponse, (desc: {
            response: PvsResponse,
            args: {
                fileName: string,
                fileExtension: string,
                contextFolder: string
            }
        }) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.latexTheoriesResponse} - param: ${desc} `,
                { actor: "server", event: serverEvent.latexTheoriesResponse, data: desc }
            ); // #DEBUG
            if(desc.response?.result && desc.response.result["main-file"] ){
                const mainFile: string = desc.response.result["main-file"];
                const mainFileFolder: string = path.dirname(mainFile);
                const mainFileExt: string = path.extname(mainFile);
                const mainFileName : string = path.basename(mainFile, mainFileExt);
                const uri: vscode.Uri = vscode.Uri.file(fsUtils.desc2fname({ fileName: mainFileName, contextFolder: mainFileFolder, fileExtension: mainFileExt}));
                const editors: readonly vscode.TextEditor[] = vscode.window.visibleTextEditors;
                const viewColumn: number = (editors && editors.length > 0) ? editors[0].viewColumn : vscode.ViewColumn.Beside;
                vscode.window.showTextDocument(uri, { preserveFocus: true, preview: true, viewColumn });
            }
        });
		this.client.onRequest(serverEvent.typecheckFileResponse, (desc: {
            response: PvsResponse,
            args: {
                fileName: string,
                fileExtension: string,
                contextFolder: string
            }
        }) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.typecheckFileResponse} - param: ${desc} `,
                { actor: "server", event: serverEvent.typecheckFileResponse, data: desc }
            ); // #DEBUG
            // request tccs for the files that typecheck correctly
            if (desc && desc.response && desc.response.result && desc.args) {
                this.client.sendRequest(serverRequest.generateTccs, {
                    fileName: desc.args.fileName,
                    fileExtension: desc.args.fileExtension,
                    contextFolder: desc.args.contextFolder,
                    quiet: true
                });
            }
            this.emitResponse("typecheckFileResponse", desc);
        });
        this.client.onNotification(serverRequest.generateTccs, (desc: {
            response: PvsContextDescriptor,
            args: {
                fileName: string,
                fileExtension: string,
                contextFolder: string
            }
        }) => {
            if (this.workspaceExplorer && desc?.response) {
                this.workspaceExplorer.updateContextFolder(desc.response, { tccDescriptor: true, theoriesFromActiveFile: this.showTheoriesFromActiveFile });
            }
        });
        this.client.onRequest(serverRequest.showTccs, (desc: {
            response: PvsContextDescriptor,
            args: FileDescriptor
        }) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverRequest.showTccs} - param: ${desc} `,
                { actor: "server", event: serverRequest.showTccs, data: desc }
            ); // #DEBUG
            if (this.workspaceExplorer && desc?.response) {
                this.workspaceExplorer.updateContextFolder(desc.response, { tccDescriptor: true, theoriesFromActiveFile: this.showTheoriesFromActiveFile });
            }
            if (desc?.args?.fileName && desc?.args?.contextFolder && desc?.response) {
                // open tcc file in the editor
                const uri: vscode.Uri = vscode.Uri.file(fsUtils.desc2fname({ fileName: desc.args.fileName, contextFolder: desc.args.contextFolder, fileExtension: ".tccs"}));
                const editors: readonly vscode.TextEditor[] = vscode.window.visibleTextEditors;
                const viewColumn: number = (editors && editors.length > 0) ? editors[0].viewColumn : vscode.ViewColumn.Beside;
                vscode.window.showTextDocument(uri, { preserveFocus: true, preview: true, viewColumn });
            }
        });
		this.client.onRequest(serverEvent.parseFileResponse, (res: PvsResponse) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.parseFileResponse} - param: ${res} `,
                { actor: "server", event: serverEvent.parseFileResponse, data: res }
            ); // #DEBUG
            // show stats
            if (res && res["math-objects"] && res.contextFolder && res.fileName) {
                // display info in the status bar
                const stats: { types: number, definitions: number, lemmas: number } = <{ types: number, definitions: number, lemmas: number }> res["math-objects"];
                this.statusBar.updateStats({ contextFolder: res["contextFolder"], fileName: res["fileName"], fileExtension: res["fileExtension"], stats });
            }
        });
		this.client.onRequest(serverEvent.workspaceStats, (res: PvsResponse) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.workspaceStats} - param: ${res} `,
                { actor: "server", event: serverEvent.workspaceStats, data: res }
            ); // #DEBUG
            // show stats
            if (res) {
                if (res["contextFolder"]) {
                    this.statusBar.setContextFolder(res["contextFolder"]);
                    if (res["math-objects"] && res["contextFolder"]) {
                        // display info in the status bar
                        const stats: { types: number, definitions: number, lemmas: number } = <{ types: number, definitions: number, lemmas: number }> res["math-objects"];
                        this.statusBar.updateStats({ contextFolder: res["contextFolder"], fileName: res["fileName"], fileExtension: res["fileExtension"], stats });
                    }
                }
            }
        });
        this.client.onRequest(serverEvent.proofCommandResponse, async (desc: ProofCommandResponse) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.proofCommandResponse} - param: ${desc} `,
                { actor: "server", event: serverEvent.proofCommandResponse, data: desc }
            ); // #DEBUG
            // notify proofexplorer
            // await this.proofExplorer.onStepExecuted(desc);
            if (desc?.res && typeof desc.res !== "string") {
                // update proof mate
                this.proofMate.updateRecommendations(desc.res);
            }
            // Trigger listeners
            this.emitResponse("proofCommandResponse", desc);
        });

        //----------------
        this.client.onNotification(serverEvent.workspaceEvent, (desc: WorkspaceEvent) => {
            this.logger?.logEvent({
                level: "info",
                actor: "server",
                source: "eventsDispatcher",
                event: serverEvent.workspaceEvent,
                action: desc?.action,
                data: this.sanitizeLogValue(desc)
            });
            switch (desc.action) {
                case "did-rename-file": {
                    const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor()
                    if (activeEditor && activeEditor.document
                            && fsUtils.isSameFile(activeEditor.document.fileName, desc.old_fname)) {
                        setTimeout(() => {
                            vscode.window.showTextDocument(vscode.Uri.file(desc.new_fname), { preserveFocus: false });
                        }, 250);
                    }
                    break;
                }
                default: {
                    console.warn(`[event-dispatcher] Warning: unrecognized prover event`, desc);
                    break;
                }
            }
        });

        //----------------
        this.client.onNotification(serverEvent.proverEvent, (desc: ProofEditEvent | ProofExecEvent) => {
            this.logger?.logEvent({
                level: desc?.action === "did-fail-to-start-proof" ? "error" : "info",
                actor: "server",
                source: "eventsDispatcher",
                event: serverEvent.proverEvent,
                action: desc?.action,
                data: this.sanitizeLogValue(desc)
            });
			switch (desc.action) {
				case "did-append-node": {
                    this.proofExplorer.didAppendNode(desc);
                    break;
                }
				case "did-copy-node": {
                    this.proofExplorer.didCopyNode(desc);
                    break;
                }
				case "did-copy-tree": {
                    this.proofExplorer.didCopyTree(desc);
                    break;
                }
                case "did-delete-node": {
                    this.proofExplorer.didDeleteNode(desc);
                    break;
                }
                case "did-cut-node": {
                    this.proofExplorer.didCutNode(desc);
                    break;
                }
                case "did-cut-tree": {
                    this.proofExplorer.didCutTree(desc);
                    break;
                }
                case "did-paste-tree": {
                    this.proofExplorer.didPasteTree(desc);
                    break;
                }
				case "did-trim-node": {
                    this.proofExplorer.didTrimNode(desc);
                    break;
                }
				case "did-rename-node": {
                    this.proofExplorer.didRenameNode(desc);
                    break;
				}
				case "did-activate-cursor": {
                    this.proofExplorer.didActivateCursor(desc);
                    break;
				}
				case "did-deactivate-cursor": {
                    this.proofExplorer.didDeactivateCursor(desc);
                    break;
				}
				case "did-update-proof-status": {
                    this.proofExplorer.didUpdateProofStatus(desc);
                    break;
                }
				case "did-start-new-proof": {
                    this.proofExplorer.enableView();
                    this.proofMate.enableView();
                    this.proofExplorer.resetView();
                    this.xterm.focus();
                    break;
                }
                case "did-fail-to-start-proof": {
                    this.proofExplorer.disableView();
                    this.proofMate.disableView();
                    this.proofExplorer.resetView();
                    let msg: string = desc.msg || "could not start prover session.";
                    msg += "\nAdditional details on the error can be inspected in the Output panel, on channel pvs-server.";
                    this.xterm.log(colorText("\nError: " + msg, PvsColor.red));
                    break;
                }
                case "did-update-dirty-flag": {
                    this.proofExplorer.updateDirtyFlag(desc);
                    break;
                }
                //---------------
                case "did-start-proof": { // this event is for interactive proof sessions
                    this.proofExplorer.didStartProof();
                    this.proofMate.startProof();
                    // await this.proofMate.loadSketchpadClips(); // loads sketchpad clips from the .jprf file
                    this.proofExplorer.focusActiveNode({ force: true }); // this will automatically open the view, in the case the view was hidden
                    this.xterm.focus();
                    break;
                }
                case "did-quit-proof": { // this is sent by CliGateway when the prover CLI is closed
                    this.proofExplorer.disposeView();
                    this.proofMate.disposeView();
                    this.statusBar.ready();
                    break;
                }
                case "did-load-sequent": {
                    this.proofExplorer.didLoadSequent(desc.sequent);
                    this.proofMate.updateRecommendations(desc.sequent);
                    break;
                }
                case "did-update-sequent": {
                    this.proofExplorer.didUpdateSequent(desc);
                    if (this.proofExplorer.isRunning()) {
                        // this.xterm.showFeedbackWhileExecuting("run-proof");
                    } else {
                        this.proofMate.updateRecommendations(desc.sequent);
                        // this.xterm.focus();
                    }
                    break;
                }
                case "did-load-proof": {
                    if (desc && desc.formula) {
                        this.proofExplorer.loadProofStructure(desc.formula, desc.desc, desc.proof);
                        this.proofMate.loadFormula(desc.formula);
                    } else {
                        window.showWarningMessage(`Failed to load proof (null descriptor)`);
                    }
                    break;
                }
                case "did-stop-running": {
                    this.proofExplorer?.didStopRunning();
                    this.proofMate?.updateRecommendations(desc?.sequent);
                    this.xterm.running(false);
                    this.xterm.showWelcomeMessage();
                    this.statusBar.running(false);
                    this.statusBar.ready();
                    break;
                }
                case "did-open-proof": {
                    if (desc && desc.formula) {
                        if (desc.proof) {
                            this.proofExplorer.loadProofStructure(desc.formula, desc.desc, desc.proof);
                            this.proofMate.loadFormula(desc.formula);
                            const fname: string = fsUtils.desc2fname(desc.formula);
                            // window.showInformationMessage(`Proof ${desc.formula.formulaName} successfully loaded from ${fname}`);
                        } else {
                            window.showWarningMessage(`Formula ${desc.formula.formulaName} does not have a proof.`);
                        }
                    } else {
                        window.showWarningMessage(`Failed to open proof (null descriptor)`);
                    }
                    break;
                }
                case "did-import-proof": {
                    if (desc && desc.formula) {
                        if (desc.proof) {
                            this.proofExplorer.loadProofStructure(desc.formula, desc.desc, desc.proof);
                            this.proofMate.loadFormula(desc.formula);
                            vscodeUtils.showInformationMessage(`Proof ${desc.importedFormula.formulaName} successfully imported!`);
                        } else {
                            vscodeUtils.showInformationMessage(`Formula ${desc.formula.formulaName} does not have a proof.`);
                        }
                    } else {
                        window.showWarningMessage(`Failed to import proof (null descriptor)`);
                    }
                    break;
                }
                default: {
                    console.warn(`[event-dispatcher] Warning: unrecognized prover event`, desc);
                    break;
                }
            }
            this.emitResponse("proverEvent", desc);
        });

        // register handler that will resolve the promise when the proof needs to be saved
        this.client.onNotification(serverRequest.saveProof, async (desc: {
            response: SaveProofResponse,
            args: {
                fileName: string,
                fileExtension: string,
                theoryName: string,
                formulaName: string,
                contextFolder: string,
                proofDescriptor: ProofDescriptor
            }
        }) => {
            this.logger?.logEvent({
                level: desc?.response?.success ? "info" : "error",
                actor: "server",
                source: "eventsDispatcher",
                event: serverRequest.saveProof,
                data: this.sanitizeLogValue(desc)
            });
            if (desc?.response?.success && desc?.response?.proofFile && desc?.response?.formula) {
                // const fname: string = fsUtils.desc2fname(desc.response.proofFile);
                if (!this.quietMode) {
                    // await this.proofMate.saveSketchpadClips();  // saves sketchpad clips to the .jprf file
                    const msg: string = `Proof ${desc.response.formula.formulaName} saved`;// in file ${fname}`;
                    vscodeUtils.showStatusBarMessage(msg);
                    // vscodeUtils.showInformationMessage(msg); // @M3 notification area gets overrun when bulk proving (prove-all)
                    // window.showInformationMessage(msg);
                }
            } else {
                if (desc?.args) {
                    if (desc?.response?.msg) {
                        vscodeUtils.showErrorMessage(`Error while saving file ${fsUtils.desc2fname(desc.args)} (${desc.response.msg})`);
                    } else {
                        vscodeUtils.showErrorMessage(`Unexpected error while saving file ${fsUtils.desc2fname(desc.args)} (please check pvs-server output for details)`);
                    }
                    if (desc?.response?.script) {
                        const fileContent: string = `# Proof for ${desc.args.formulaName}\n`
                            + 'An error occurred while trying to save your proof in PVS.\n'
                            // + 'You might be using an obsolete version of PVS. Please try to re-install PVS with the command `M-x reinstall-pvs`.\n'
                            // + 'The command will open a dialog, select `Download PVS` to install the latest version of PVS.\n'
                            + `If the problem persists, please report an issue on [github](https://github.com/nasa/vscode-pvs/issues) or on the [PVS group](https://groups.google.com/g/pvs-group), we will look into it.\n\n`
                            + `## Your proof attempt\n`
                            + `Don't panic, your proof attempt for ${desc.args.formulaName} is not lost.<br>\n`
                            + `VSCode-PVS saved your proof attempt, and you can restore it from the Proof Explorer menu **...** -> **Restore Proof**<br>\n\n`
                            + `If everything else fails, below you can find the complete proof script, which you can paste in the prover terminal to repeat the proof:\n`
                            + '```lisp\n'
                            + desc.response.script
                            + '\n```';
                        const fdesc: FileDescriptor = {
                            fileName: desc.args.formulaName,
                            fileExtension: ".md",
                            contextFolder: vscodeUtils.getPreviewFolder(),
                            fileContent
                        };
                        await vscodeUtils.showMarkdownPreview(fdesc);
                    }
                }
            }
        });


        this.client.onRequest(serverEvent.proveFormulaResponse, (desc: ProveFormulaResponse) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.proveFormulaResponse} - param: ${desc} `,
                { actor: "server", event: serverEvent.proveFormulaResponse, data: desc }
            ); // #DEBUG
            // console.log(`[${fsUtils.generateTimestamp()}] `+desc);
            // if (desc) {
            //     // initialise proof explorer
            //     // this.proofExplorer.setLogFileName(desc);
            //     // this.proofExplorer.setShasum(desc.shasum);

            //     if (desc.response && desc.response.result) {
            //         // update proof mate
            //         this.proofMate.setProofDescriptor(desc.args);
            //         this.proofMate.updateRecommendations(desc.response.result);
            //         // save initial proof state in proof explorer
            //         // this.proofExplorer.loadInitialProofState(desc.response.result);
            //     }
            //     // start proof
            //     // this.proofExplorer.startProof();
            //     this.proofMate.startProof();
            // }
            this.emitResponse("proveFormulaResponse", desc);
        });

        this.client.onRequest(serverEvent.pvsServerFail, (desc: { msg?: string }) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.pvsServerFail} - param: ${desc} `,
                { level: "error", actor: "server", event: serverEvent.pvsServerFail, data: desc }
            ); // #DEBUG
            desc = desc || {};
            if (desc.msg) {
                this.statusBar.failure(desc.msg);
            }
        });

        this.client.onRequest(serverEvent.serverModeUpdateEvent, (desc: { mode: ServerMode }) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.serverModeUpdateEvent} - param: ${desc} `,
                { actor: "server", event: serverEvent.serverModeUpdateEvent, data: desc }
            ); // #DEBUG
            if (desc) {
                switch (desc.mode) {
                    case "in-checker": {
                        this.inChecker = true;
                        this.inEvaluator = false;
                        vscode.commands.executeCommand('setContext', 'in-checker', true);
                        vscode.commands.executeCommand('setContext', 'in-evaluator', false);
                        break;
                    }
                    case "pvsio": {
                        this.inChecker = false;
                        this.inEvaluator = true;
                        vscode.commands.executeCommand('setContext', 'in-checker', false);
                        vscode.commands.executeCommand('setContext', 'in-evaluator', true);
                        break;
                    }
                    case "lisp":
                    default: {
                        this.inChecker = false;
                        this.inEvaluator = false;
                        vscode.commands.executeCommand('setContext', 'in-checker', false);
                        vscode.commands.executeCommand('setContext', 'in-evaluator', false);
                        // disable treeviz controls
				        this.proofExplorer?.disableTreeVizControls();
                        break;
                    }
                }
                this.proofExplorer.didUpdateServerMode(desc.mode);
                this.workspaceExplorer.refreshView();
                this.emitResponse("serverModeUpdateEvent", desc);
            }
        });

		this.client.onNotification(serverRequest.getContextDescriptor, (desc: PvsContextDescriptor) => {
            this.showTheoriesFromActiveFile = vscodeUtils.getConfigurationFlag("pvs.pvsWorkspaceTheoriesFromActiveFile");
            // publish variable in the global space that can be useful for enabling WorkspaceExplorer inline commands defined in package.json
            vscode.commands.executeCommand('setContext', 'theories-from-active-file', this.showTheoriesFromActiveFile);
            this.workspaceExplorer?.updateContextFolder(desc, { theoriesFromActiveFile: this.showTheoriesFromActiveFile });
        });

		// this.client.onRequest(serverEvent.querySaveProof, async (request: {
		//   console.log(`[${fsUtils.generateTimestamp()}] `+`[eventsDispatcher] responding request ${serverEvent.querySaveProof} - param: ${JSON.stringify(request)} `); // #DEBUG
        //     args: PvsProofCommand
		// }) => {
        //     if (request) {
        //         await this.proofExplorer.queryQuitProofAndSave();
        //     } else {
        //         console.error(`[events-dispatcher] Error: null request in quitProofEvent`);
        //     }
        // });

		this.client.onRequest(serverEvent.QED, async (desc: {
            response: { result: "Q.E.D." },
            request: PvsProofCommand
		}) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.QED} - param: ${desc} `,
                { actor: "server", event: serverEvent.QED, data: desc }
            ); // #DEBUG
            // annotate pvs file with @QED at the formula location
            console.log(`[${fsUtils.generateTimestamp()}] `+desc);
            const flag: boolean = vscodeUtils.getConfigurationFlag("pvs.settings.prover.@QED");
            if (flag) {
                const formula: PvsFormula = desc?.request;
                if (formula && formula.line && formula.fileName && formula.fileExtension
                        && formula.contextFolder && formula.formulaName) {
                    await vscodeUtils.annotateFormula(formula, "@QED");
                }
            }
            // these are commented out because we want to keep sketchpad and clips across prover sessions
            // this.proofMate.clearSketchPath();
            // this.proofMate.saveSketchpadClips();
        });

        this.client.onRequest(serverEvent.showTheorySummaryResponse, (desc: {
            response: FileDescriptor,
            args: PvsTheory
        }) => {
            this.log(
                `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.showTheorySummaryResponse} - param: ${desc} `,
                { actor: "server", event: serverEvent.showTheorySummaryResponse, data: desc }
            ); // #DEBUG
            if (desc && desc.response) {
                vscodeUtils.showTextDocument(desc.response);
            }
        });

        this.client.onNotification(serverEvent.profilerData, (data: string) => {
            this.logger.profilerData(data);
        });

        this.client.onNotification("pvs.progress-info", (msg: string) => {
            this.statusBar.showProgress(msg);
        });


        //---------------------------------------------------------
        // commands invoked using code lens, emacs bindings, explorer, etc
        //---------------------------------------------------------

        context.subscriptions.push(this.registerCommand(quickFixAddImportingCommand, async (desc: QuickFixAddImporting): Promise<boolean> => {
            if (desc?.newImporting && desc?.position && desc?.fileName && desc?.fileExtension) {
                return await quickFixAddImporting(desc);
            }
            return false;
        }));
        context.subscriptions.push(this.registerCommand(quickFixReplaceCommand, async (desc: QuickFixReplace): Promise<boolean> => {
            if (desc?.newText && desc?.range && desc?.fileName && desc?.fileExtension) {
                return await quickFixReplace(desc);
            }
            return false;
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.insert-prooflite-script", async (desc: PvsFormula) => {
            if (!(desc.fileName && desc.fileExtension && desc.contextFolder && desc.theoryName && desc.formulaName)) {
                const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
                const document: vscode.TextDocument = activeEditor?.document;
                const line: number = window?.activeTextEditor?.selection?.active ? activeEditor?.selection?.active?.line : 0;
                desc = document ? {
                    fileName: fsUtils.getFileName(document.fileName),
                    fileExtension: fsUtils.getFileExtension(document.fileName),
                    contextFolder: fsUtils.getContextFolder(document.fileName),
                    theoryName: fsUtils.findTheoryName(document.getText(), line),
                    formulaName: fsUtils.findFormulaName(document.getText(), line),
                    line
                } : null;
            }
            if (desc) {
                // try to fetch prooflite script
                try {
                    const proofliteFile: FileDescriptor = await this.workspaceExplorer?.generateProofliteFileWithProgress(desc);
                    if (proofliteFile?.fileContent) {
                        // insert prooflite script at cursor position
                        const script: string = proofliteFile?.fileContent;
                        vscodeUtils.insertTextAtCursorPosition(utils.commentProofliteScript(script));
                    } else {
                        vscodeUtils.showWarningMessage("Warning: Could not generate prooflite script");
                    }
                } catch {
                    vscodeUtils.showWarningMessage("Warning: Could not generate prooflite script");
                }
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.progress-info", (msg: string) => {
            this.statusBar.showProgress(msg);
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.comment-prooflite-line", () => {
            vscodeUtils.commentProofliteInActiveEditor();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.search-nasalib", () => {
            this.search.reveal(); // async call
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.view-prelude-file", () => {
            this.client.sendRequest(serverRequest.viewPreludeFile);
            this.client.onRequest(serverEvent.viewPreludeFileResponse, (desc: PvsFile) => {
                this.log(
                    `[${fsUtils.generateTimestamp()}] ` + `[eventsDispatcher] responding request ${serverEvent.viewPreludeFileResponse} - param: ${desc} `,
                    { actor: "server", event: serverEvent.viewPreludeFileResponse, data: desc }
                ); // #DEBUG
                vscodeUtils.showTextDocument(desc);
            });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.update-pvs", async () => {
            await this.packageManager.pvsInstallationWizard({ update: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.select-pvs-path", async () => {
            await this.packageManager.pvsInstallationWizard({
				msg: `Please choose one of the following actions.\n`,
				update: true,
				preferDefaultFolder: true
			});
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.open-vscode-pvs-settings", async () => {
            vscodeUtils.openVscodePvsSettings();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.set-pvs-path", () => {
            this.packageManager.choosePvsPath();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.install-nasalib", () => {
            this.statusBar.hideDownloadNasalibButton();
            this.packageManager.nasalibInstallationWizard();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.update-nasalib", () => {
            this.statusBar.hideDownloadNasalibButton();
            this.packageManager.nasalibInstallationWizard({ update: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.add-pvs-library", async () => {
            await vscodeUtils.addPvsLibraryFolderWizard();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.reset-pvs-library-path", async () => {
            await vscodeUtils.clearPvsLibraryPath();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.view-pvs-library-path", async () => {
            commands.executeCommand('workbench.action.openSettings', `${vscodeUtils.extensionName} pvs-library-path`);
        }));
        // vscode-pvs.send-proof-command
        context.subscriptions.push(this.registerCommand("vscode-pvs.send-proof-command", (desc: PvsProofCommand) => {
            this.client.sendRequest(serverRequest.proofCommand, desc);
            this.xterm.showFeedbackWhileExecuting(desc?.cmd || "");
        }));
        context.subscriptions.push(this.registerCommand("xterm.showFeedbackWhileExecuting", (desc: { cmd: string, target?: string }) => {
            this.xterm.showFeedbackWhileExecuting(desc?.cmd, desc?.target);
        }));
        context.subscriptions.push(this.registerCommand("xterm.did-execute-command", (desc: { cmd: string, target?: string }) => {
            if (!this.proofExplorer.isRunning() && !this.proofMate.isRunning()) {
                this.xterm.running(false);
                this.xterm.showWelcomeMessage();
                this.statusBar.running(false);
                this.statusBar.ready();
            } else {
                this.xterm.running(true);
                this.statusBar.running(true);
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.select-profile", (desc: { profile: ProofMateProfile }) => {
            // this.vscodePvsTerminal.selectProfile(desc);
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.new-pvs-file", async (resource: { path: string }) => {
            const activeFolder: string = fsUtils.getContextFolder(vscodeUtils.getActivePvsFile()?.fileName) || vscodeUtils.getRootPath();
            const contextFolder: string = resource?.path || activeFolder;
            this.log(`[${fsUtils.generateTimestamp()}] ` + contextFolder, {
                actor: this.getCurrentActor(resource),
                event: "vscode-pvs.new-pvs-file",
                data: { contextFolder }
            });
            this.workspaceExplorer.newPvsFileDialog(contextFolder); // async method
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.new-pvs-theory", async () => {
            this.workspaceExplorer.newPvsTheoryDialog(); // async method
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.open-pvs-file", async () => {
            this.workspaceExplorer.openPvsFile(); // async method
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.goto-pvs-file", async (desc: GotoFileDescriptor) => {
            this.workspaceExplorer.openPvsFile(desc, { preserveFocus: false}); // async method
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.open-pvs-file-or-folder", async () => {
            await this.workspaceExplorer.openPvsFileOrFolder();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.open-pvs-workspace", async () => {
            this.workspaceExplorer.openWorkspace(); // async method
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.clean-pvs-workspace", async () => {
            this.workspaceExplorer.cleanPvsWorkspace(); // async method
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.show-version-info", () => {
            // this.statusBar.showVersionInfo();
            this.statusBar.showVersionDialog({ downloadButtons: false });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.show-version-dialog", () => {
            this.statusBar.showVersionDialog({ downloadButtons: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.reboot-pvs", async (arg?: string | { info?: string; force?: boolean; cleanFolder?: boolean }) => {
            const opt = typeof arg === "string" ? { info: arg } : (arg || {});
            // ask the user confirmation before restarting pvs unless force is true
			const yesNo: string[] = [ "Yes", "No" ];
			const msg: string = opt.info || `Reboot pvs?\n\nThis action can resolve situations where the server crashed or is not responding.`;
			const ans: string | undefined = opt.force ? yesNo[0] : await vscode.window.showInformationMessage(msg, { modal: true }, yesNo[0]);
			if (ans === yesNo[0]) {
                if (opt.cleanFolder) {
                    await vscodeUtils.cleanPvsWorkspace();
                }
                const currentContext: string = vscodeUtils.getRootPath();
                const req = {
                    cleanFolder: opt.cleanFolder ? currentContext : undefined,
                    externalServer: vscodeUtils.getConfigurationFlag("pvs.externalServer"),
                    webSocketPort: vscodeUtils.getConfigurationValue("pvs.initialPortNumber")
                };
                // Cancel any active prove-theory execution and unblock waiting responses
                this.emitResponse("pvsServerRebooting", { msg: "PVS server was restarted" });
                this.workspaceExplorer?.pvsFailureHandler?.({ msg: "PVS server was restarted", src: "reboot-pvs" });
                this.client.sendRequest(serverRequest.rebootPvsServer, req);
                // terminate any prover/evaluator session and reset views
                this.proofExplorer?.disposeView();
                this.proofMate?.disposeView();
                this.xterm?.dispose();
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.interrupt-prover", async () => {
            // ask the user confirmation before restarting pvs
            if (this.proofExplorer.isRunning()) {
                this.proofExplorer.queryPauseProof();
            } else {
                const yesNo: string[] = [ "Yes", "No" ];
                const msg: string = `Interrupt the execution of the current proof command?`;
                const ans: string | undefined = await vscode.window.showInformationMessage(msg, { modal: true }, yesNo[0])
                if (ans === yesNo[0]) {
                    const action: ProofExecInterruptProver = { action: "interrupt-prover" };
                    this.client.sendRequest(serverRequest.proverCommand, action);
                }
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.interrupt-pvs", async () => {
            commands.executeCommand("vscode-pvs.reboot-pvs", "Interrupt the execution of the current PVS command?");
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.ready", () => {
            this.statusBar.ready();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.show-hidden-formulas", async (desc: { cmd: string }) => {
            if (this.xterm) {
                this.xterm?.write("(show-hidden-formulas)");
                this.xterm?.sendTextToServer("(show-hidden-formulas)");
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.show-expanded-sequent", async (desc: { cmd: string }) => {
            if (this.xterm) {
                this.xterm?.write("(show-expanded-sequent)");
                this.xterm?.sendTextToServer("(show-expanded-sequent)");
            }
        }));
        context.subscriptions.push(this.registerCommand("xterm-pvs.send-command", async (desc: { cmd: string }) => {
            if (this.xterm && desc?.cmd?.trim()) {
                if (this.uiDebouncer) {
                    // do nothing - this prevents double clicks on the widget
                } else {
                    // wait 300ms to rule out double click
                    this.uiDebouncer = setTimeout(async () => {
                        this.xterm?.write(desc.cmd);
                        await this.xterm?.sendTextToServer(desc.cmd);
                        this.uiDebouncer = null;
                    }, 300);
                }
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.interrupt-and-quit-prover", async () => {
            // ask the user confirmation before restarting pvs
            const action: ProofExecInterruptAndQuitProver = { action: "interrupt-and-quit-prover" };
            this.client.sendRequest(serverRequest.proverCommand, action);
            this.statusBar.ready();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.download-nasalib", async () => {
            this.statusBar.hideDownloadNasalibButton();
            const success: boolean = await this.packageManager.nasalibInstallationWizard();
            if (success) {
                this.statusBar.hideDownloadNasalibButton();
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.report-issue", async () => {
            this.client.outputChannel.show(false);
            await vscode.commands.executeCommand("workbench.action.output.toggleOutput", true);
            await vscode.commands.executeCommand("workbench.action.openActiveLogOutputFile");
            await vscode.commands.executeCommand("copyRelativeFilePath");
            await vscode.commands.executeCommand("workbench.action.closeActiveEditor");
            await vscode.commands.executeCommand("workbench.action.closePanel");
            this.client.outputChannel.show(false);

            // @M3 Since version 8.0, PVS stores log information in the
            //     folder ~/.pvslog, let's use the same folder to store
            //     our log file.
            const logFolder: string = path.join(fsUtils.HOME_DIR, ".pvslog");
            const vscodePvsLogFile: string = await vscode.env.clipboard.readText();

            // @M3 get latest PVS log file
            const files: string[] = fs.readdirSync(logFolder);
            const filteredFiles: { file: string; mtime: Date; }[] = files.filter(file => new RegExp(
                "pvs-[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]\.log"
            ).test(file)).map(file => {
                const filePath = path.join(logFolder, file);
                const stats = fs.statSync(filePath);
                return { file, mtime: stats.mtime };
            });
            const pvsLogFileName: string = (filteredFiles.length > 0) ? filteredFiles.reduce((prev, curr) => {
                    return (prev.mtime > curr.mtime) ? prev : curr;
            }).file : null;
            const pvsLogFile: string = pvsLogFileName ? path.join(logFolder, pvsLogFileName) : null;

            const ok: string = "Ok";
            const item = await window.showInformationMessage(`Report Issue                                                              `, {
                modal: true,
                detail:
`Please send a brief description of the issue, along with the following log ${pvsLogFile ? "files": "file"} (which will now be opened in the editor):

• ${vscodePvsLogFile}
${pvsLogFile ? `• ${pvsLogFileName}
`: ""}

to

mariano.m.moscato@nasa.gov

Disclaimer: the logs could contain information about the system, such as name of the theories you were working on, location of PVS files in your installation, etc. Please review the log ${pvsLogFile ?
    "files": "file"} before sending ${pvsLogFile ? "them": "it"} and remove any information you do not want to share. No guarantee that issues would be addressed should be assumed.`
            }, ok);//{ isCloseAffordance: true, title: "Ok" });

            if (item === ok) {
                // open vscode-pvs output channel as an editor window
                this.client.outputChannel.show(true);
                await vscode.commands.executeCommand("workbench.action.openActiveLogOutputFile");
                this.client.outputChannel.hide();
                // open pvs log file, if any
                if (pvsLogFile) {
                    const pvsLogDocument: vscode.TextDocument = await vscode.workspace.openTextDocument(vscode.Uri.file(pvsLogFile));
                    await vscode.languages.setTextDocumentLanguage(pvsLogDocument, "log");
                    vscode.window.showTextDocument(pvsLogDocument, { viewColumn: vscode.ViewColumn.Active, preserveFocus: true, preview: false });
                }
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.install-pvs", async () => {
            this.statusBar.hideinstallpvsButton();
            const success: boolean = await this.packageManager.pvsInstallationWizard();
            if (!success) {
                this.statusBar.showInstallPvsButton();
            } else {
                setTimeout(async () => {
                    await this.packageManager.nasalibInstallationWizard();
                }, 2000);
            }
        }));

        // context.subscriptions.push(commands.registerCommand("proof-explorer.step-command", (desc: { fileName: string, fileExtension: string, contextFolder: string, theoryName: string, formulaName: string, cmd: string }) => {
        //     if (desc && desc.cmd) {
        //         this.vscodePvsTerminal.sendProofCommand(desc, { addNewLine: true });
        //         // window.showInformationMessage(`${desc.cmd} sent to terminal`)
        //     }
        // }));
        context.subscriptions.push(this.registerCommand("proof-mate.proof-command-dblclicked", (desc: PvsProofCommand) => {
            if (desc?.cmd) {
                this.xterm.sendText(desc.cmd);
                this.xterm.focus();
                this.xterm.updateHelp();
                // window.showInformationMessage(`${desc.cmd} sent to terminal`)
            }
        }));
        context.subscriptions.push(this.registerCommand("proof-explorer.proof-command-dblclicked", (desc: PvsProofCommand) => {
            if (desc?.cmd) {
                this.xterm.sendText(desc.cmd);
                this.xterm.focus();
                this.xterm.updateHelp();
                // window.showInformationMessage(`${desc.cmd} sent to terminal`)
            }
        }));
        context.subscriptions.push(this.registerCommand("xterm-pvs.focus", () => {
            this.xterm.focus();
        }));

        context.subscriptions.push(this.registerCommand("proof-mate.update-sketchpad", (desc: { items: ProofItem[], running?: boolean }) => {
            if (desc) {
                const formulaName: string = this.proofExplorer.getFormulaName();
                const label: string = formulaName ? `${new Date().toLocaleString()} ${formulaName}` : `${new Date().toLocaleString()}`;
                const success: boolean = this.proofMate.add({ items: desc.items }, {
                    select: true,
                    markSelectedAsActive: true,
                    label,
                    focus: desc.running
                });
                return success;
            }
        }));

        context.subscriptions.push(this.registerCommand("vscode-pvs.print-warning-message-in-terminal", (desc: { fileName: string, fileExtension: string, contextFolder: string, theoryName: string, formulaName: string, cmd: string }) => {
            // TODO
            // this.vscodePvsTerminal.printWarningMessage(desc);
        }));

        // vscode-pvs.metax
        context.subscriptions.push(this.registerCommand("vscode-pvs.metax", () => {
            this.emacsBindings.metaxPrompt();
        }));

        context.subscriptions.push(this.registerCommand("vscode-pvs.ctrlU", () => {
            this.emacsBindings.metaxPrompt(true);
        }));

        //         // if the file is currently open in the editor, save file first
        //         await vscode.window.activeTextEditor.document.save();
        //         let formula: PvsFormula = resource2desc(vscode.window.activeTextEditor.document.fileName);

        // // const document: vscode.TextDocument = window.activeTextEditor.document;
        // const info: { content: string, line: number } = {
        //     content: vscode.window.activeTextEditor.document.getText(),
        //     line: vscode.window.activeTextEditor.selection.active.line
        // };
        // desc.theoryName = info.content ? fsUtils.findTheoryName(info.content, info.line) : null;
        // desc.formulaName = desc.theoryName ? fsUtils.findFormulaName(info.content, info.line) : null;

        // vscode-pvs.show-prooflite
        context.subscriptions.push(this.registerCommand("vscode-pvs.show-prooflite", async (resource: string | { path: string } | { contextValue: string }) => {
            const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
            if (!resource && activeEditor?.document?.fileName) {
                resource = { path: activeEditor.document.fileName };
            }
            if (resource) {
                const desc: PvsFormula = vscodeUtils.resource2pvsFormula(resource);
                // ask the user confirmation of what needs to be done: view existing prooflite, generate prooflite
                const viewOrGenerate: string[] = [ "View Existing Prooflite", "Generate Prooflite" ];
                const msg: string = `Show Prooflite for formula ${desc.formulaName}?`;
                const ans: string = await vscode.window.showInformationMessage(msg, { modal: true, detail: "Press 'Esc' to Cancel" }, viewOrGenerate[0], viewOrGenerate[1]);
                if (ans === viewOrGenerate[0]) {
                    // view existing prooflite
                    await this.workspaceExplorer.viewProofliteFile(desc, { showFileInEditor: true });
                } else if (ans === viewOrGenerate[1]) {
                    // (re-)generate prooflite file
                    try {
                        await this.workspaceExplorer.generateProofliteFileWithProgress(desc, { showFileInEditor: true });
                    } catch { }
                } // else do nothing, the user cancelled the request

                // if (!desc.theoryName) {
                //     // const document: vscode.TextDocument = window.activeTextEditor.document;
                //     const info: { content: string, line: number } = (resource && resource["path"]) ? { content: await fsUtils.readFile(resource["path"]), line: 0 }
                //             : { content: window.activeTextEditor.document.getText(), line: window.activeTextEditor.selection.active.line };
                //     const theoryName: string = fsUtils.findTheoryName(info.content, info.line);
                //     desc.theoryName = theoryName;
                // }
                // if (desc) {
                //     if (!desc.theoryName) {
                //         // const document: vscode.TextDocument = window.activeTextEditor.document;
                //         const info: { content: string, line: number } = (resource && resource["path"]) ? { content: await fsUtils.readFile(resource["path"]), line: 0 }
                //                 : { content: window.activeTextEditor.document.getText(), line: window.activeTextEditor.selection.active.line };
                //         const theoryName: string = fsUtils.findTheoryName(info.content, info.line);
                //         desc.theoryName = theoryName;
                //     }
                //     if (desc.theoryName) {
                //         // show dialog with progress
                //         await window.withProgress({
                //             location: ProgressLocation.Notification,
                //             cancellable: true
                //         }, async (progress, token) => {
                //             // show initial dialog with spinning progress
                //             const message: string = `Generating ProofLite script for formula ${desc.formulaName}`;
                //             progress.report({ increment: -1, message });

                //             return new Promise<void>((resolve, reject) => {
                //                 this.client.sendRequest(serverRequest.showProofLite, desc);
                //                 this.client.onRequest(serverEvent.showProofLiteResponse, async (desc: {
                //                     response: { proofFile: FileDescriptor },
                //                     args: PvsFormula
                //                 }) => {
                //                     if (desc && desc.args && desc.response && desc.response.proofFile) {
                //                         const line: number = await fsUtils.getProofLitePosition({ formula: desc.args, proofFile: desc.response.proofFile });
                //                         vscodeUtils.showTextDocument(desc.response.proofFile, {
                //                             viewColumn: vscode.ViewColumn.Beside,
                //                             selection: new vscode.Range(
                //                                 new vscode.Position(line - 1, 0),
                //                                 new vscode.Position(line, 0)
                //                             )
                //                         });
                //                         this.statusBar.ready();
                //                         progress.report({ message: `Done!`, increment: 100 });
                //                         resolve();
                //                         // vscodeUtils.previewTextDocument(`${desc.args.theoryName}.prlite`, desc.response, {
                //                         //     contextFolder: path.join(desc.args.contextFolder, "pvsbin"),
                //                         //     viewColumn: vscode.ViewColumn.Beside
                //                         // });
                //                     } else {
                //                         progress.report({ message: `${utils.icons.bang} Unable to generate prooflite script for formula ${desc.args.formulaName}`, increment: 100 });
                //                         setTimeout(() => {
                //                             resolve();
                //                         }, 4000)
                //                     }
                //                 });
                //             });
                //         });
                //     } else {
                //         vscodeUtils.showErrorMessage(`Error while trying to display prooflite script (could not identify theory name, please check that the file typechecks correctly)`);
                //     }
                // } else {
                //     console.error("[vscode-events-dispatcher] Error: prooflite script requested for unknown resource", resource);
                // }
            }
        }));

        context.subscriptions.push(this.registerCommand("vscode-pvs.pvsio-web", async (resource: PvsTheory /*| { path: string }*/, opt?: { force?: boolean }) => {
            let req: StartXTermEvaluatorRequest = resource && resource["theoryName"] ? <PvsTheory> resource : null;
            if (!req) {
                const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
                const fname: string = activeEditor?.document?.fileName;
                if (fname) {
                    const contextFolder: string  = fsUtils.getContextFolder(fname);
                    const fileName: string = fsUtils.getFileName(fname);
                    const fileExtension: string = fsUtils.getFileExtension(fname);
                    const line: number = activeEditor?.selection?.active?.line || 0;
                    const fileContent: string = fsUtils.readFile(fname);
                    const theoryName: string = fsUtils.findTheoryName(fileContent, line);
                    req = {
                        contextFolder,
                        theoryName,
                        fileName,
                        fileExtension
                    };
                } else {
                    // check if there's a pvsio session
                    req = this.xterm!.getTheory();
                }
            }
            if (req && req.contextFolder && req.theoryName && req.fileName && req.fileExtension) {
                // ask the user confirmation before restarting pvs
                const yesno: string[] = [ "Yes", "No" ];
                const msg: string = `Start PVSio-web for theory ${req.theoryName}?`;
                const ans: string = opt?.force ? yesno[0] : await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0]);
                if (ans === yesno[0]) {
                    // dispose any previous instance
                    await this.pvsIoWeb.dispose();
                    // start pvsio
                    vscodeUtils.showInformationMessage("Loading evaluator back-end, please wait...");
                    const success: boolean = await this.xterm.onStartEvaluatorRequest(req);
                    if (success) {
                        const theory: PvsTheory = this.xterm.getTheory();
                        if (theory) {
                            // create a new instance
                            this.pvsIoWeb.setTheory(theory);
                            this.pvsIoWeb.setTerminal(this.xterm);
                            await this.pvsIoWeb.reveal();
                        }
                    } else {
                        vscodeUtils.showWarningMessage("Unable to create a new PVSio Evaluator session");
                    }
                }
            } else {
                vscodeUtils.showWarningMessage("Unable to start PVSio-web, please open a PVS file first");
            }
        }));
        // pvsio-evaluator
        context.subscriptions.push(this.registerCommand("vscode-pvs.pvsio-evaluator", async (theory?: PvsTheory) => {
            return await this.xterm.onStartEvaluatorRequest(theory);
        }));
        // io requests (pvsio, pvsio-web)
        context.subscriptions.push(this.registerCommand("vscode-pvs.io", async (resource?: { path: string }) => {
            // the toolbar generates invocations with resource = { path }, where path is the path of the file opened in the active editor
            const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
            if (activeEditor?.document) {
                // if the file is currently open in the editor, save file first
                await activeEditor.document.save();
                if (!resource) {
                    resource = { path: activeEditor.document.fileName };
                }
            }
			if (resource) {
                const desc: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (isPvsFile(desc)) {
                    const msg: string = "Start evaluator session?";
                    const selection: string[] = [ "Start PVSio", "Start PVSio-Web" ];
                    const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, selection[0], selection[1]);
                    switch (ans) {
                        case selection[0]: { return vscode.commands.executeCommand("vscode-pvs.pvsio-evaluator"); }
                        case selection[1]: { return vscode.commands.executeCommand("vscode-pvs.pvsio-web", resource, { force: true }); }
                        default: {
                            break;
                        }
                    }
                } else {
                    showWarningMessage (`The pvs evaluator can only be used on .pvs files.`);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));

        // ignore keypress
        context.subscriptions.push(this.registerCommand("vscode-pvs.ignore-keypress", () => {}));

        // quick-open
        context.subscriptions.push(this.registerCommand("vscode-pvs.quick-open", (desc: FollowLink) => {
            if (desc?.fname) {
                this.fileViewer.open(fsUtils.fname2desc(desc.fname));
                // vscode.commands.executeCommand("workbench.action.quickOpen", desc.fname);
            }
        }));
        // prettyprint-expanded
        context.subscriptions.push(this.registerCommand("vscode-pvs.prettyprint-expanded", (desc: PvsFile) => {
            if (desc?.fileName) {
                this.client.sendRequest(serverRequest.prettyprintExpanded, { file: desc }); // async call
                this.client.onNotification(serverRequest.prettyprintExpanded, (res: PrettyPrintExpandedResponse) => {
                    vscodeUtils.previewTextDocument(res.ans.fileName + res.ans.fileExtension, res.ans.fileContent, {
                        contextFolder: res.ans.contextFolder,
                        viewColumn: vscode.ViewColumn.Beside
                    });
                });
            }
        }));
        // view-as-markdown
        context.subscriptions.push(this.registerCommand("vscode-pvs.view-as-markdown", (desc: PvsFile) => {
            if (desc?.fileName) {
                this.fileViewer.openAsMarkdownPreview(desc); // async call
                // vscode.commands.executeCommand("workbench.action.quickOpen", desc.fname);
            }
        }));

        // document-theory
        context.subscriptions.push(this.registerCommand("vscode-pvs.document-theory", async (desc: PvsTheory) => {
            commands.executeCommand('vscode-pvs.pvs-doc', desc);
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.pvs-doc", async (desc: PvsTheory) => {
            if (desc?.theoryName) {
                this.fileViewer.pvsDocInteractive(desc); // async call
            }
        }));

        // evaluate expression and open
        context.subscriptions.push(this.registerCommand("vscode-pvs.open-path-expression", async (resource: {
            path: string, expr: string
        }) => {
            const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
            if (resource) {
                let desc: PvsTheory = vscodeUtils.resource2pvsTheory(resource);
                if (desc) {
                    if (!desc.theoryName) {
                        const info: { content: string, line: number } = (resource["path"]) ? { content: fsUtils.readFile(resource["path"]), line: 0 }
                            : { content: activeEditor?.document?.getText(), line: activeEditor?.selection?.active?.line };
                        const theoryName: string = fsUtils.findTheoryName(info.content, info.line);
                        desc.theoryName = theoryName;
                    }
                    if (desc.theoryName) {
                        const selection: Selection = activeEditor?.selection;
                        const expr: string = resource["expr"] || activeEditor?.document?.getText(selection);
                        if (expr) {
                            const request: EvalExpressionRequest = {
                                contextFolder: desc.contextFolder,
                                fileName: desc.fileName,
                                fileExtension: desc.fileExtension,
                                theoryName: desc.theoryName,
                                expr
                            };
                            this.pathEvaluator.evaluateAndOpen(request);
                        }
                    } else {
                        vscodeUtils.showErrorMessage(`Error while trying to invoke open-path-expression (could not identify theory name, please check that the file typechecks correctly)`);
                    }
                } else {
                    this.logError("[vscode-events-dispatcher] Error: open-path-expression invoked over an unknown resource", resource);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: open-path-expression invoked with null resource", resource);
            }
        }));


        // pvsio-plot
        context.subscriptions.push(this.registerCommand("vscode-pvs.plot-expression", async (resource: string | {
            path: string, expr?: string
        } | {
            contextValue: string
        } | {
            fileName?: string,
            fileExtension?: string,
            contextFolder?: string,
            theoryName?: string,
            expr?: string
        }) => {
            const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
            if (activeEditor?.document) {
                // if the file is currently open in the editor, save file first
                await activeEditor.document.save();
                if (!resource) {
                    resource = { path: activeEditor.document.fileName };
                }
            }
            if (resource) {
                let desc: PvsTheory = vscodeUtils.resource2pvsTheory(resource);
                if (desc) {
                    if (!desc.theoryName) {
                        const possibleContent = activeEditor?.document?.getText();
                        const info: { content: string, line: number } = // (resource["path"])
                        !possibleContent
                        ? { content: fsUtils.readFile((<{ path: string }>resource)["path"]), line: 0 }
                            : { content: activeEditor?.document?.getText(), line: activeEditor?.selection?.active?.line };
                        const theoryName: string = fsUtils.findTheoryName(info.content, info.line);
                        desc.theoryName = theoryName;
                    }
                    if (desc.theoryName) {
                        const selection: Selection = activeEditor?.selection;
                        const expr: string = (<{ expr: string }>resource)["expr"] || activeEditor?.document?.getText(selection);
                        if (expr) {
                            const request: EvalExpressionRequest = {
                                contextFolder: desc.contextFolder,
                                fileName: desc.fileName,
                                fileExtension: desc.fileExtension,
                                theoryName: desc.theoryName,
                                expr
                            };
                            this.plotter.plot(request);
                        }
                    } else {
                        vscodeUtils.showErrorMessage(`Error while trying to invoke PVSio (could not identify theory name, please check that the file typechecks correctly)`);
                    }
                } else {
                    this.logError("[vscode-events-dispatcher] Error: pvsio-evaluator invoked over an unknown resource", resource);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: pvsio-evaluator invoked with null resource", resource);
            }
        }));

        // vscode-pvs.jprove-formula
        context.subscriptions.push(this.registerCommand("vscode-pvs.jprove-formula", async (desc: {
            contextFolder: string,
            fileName: string,
            fileExtension: string,
            theoryName: string,
            formulaName: string
        }) => {
            if (desc) {
                commands.executeCommand("vscode-pvs.prove-formula", {
                    contextFolder: desc.contextFolder,
                    fileName: desc.fileName,
                    fileExtension: desc.fileExtension,
                    theoryName: (desc.fileExtension === ".tccs" && desc.theoryName.endsWith("_TCCS")) ? desc.theoryName.substring(0, desc.theoryName.length - 5) : desc.theoryName,
                    formulaName: desc.formulaName,
                    proofFile: {
                        contextFolder: desc.contextFolder,
                        fileName: desc.fileName,
                        fileExtension: ".jprf"
                    }
                });
                this.statusBar.showProgress(`Starting J-PRF proof for ${desc.formulaName}`);
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.copy-prooflite", async (req: CopyProofliteRequest) => {
            if (req?.prooflite && req?.formulaName) {
                // copy prooflite script to system clipboard
                vscodeUtils.copyToClipboard(utils.commentProofliteScript(req.prooflite), { msg: `Prooflite ${req.formulaName} copied to clipboard`, useDialog: true });
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-formula-at-cursor-position", async () => {
            this.proofExplorer.proveFormulaAtCursorPosition();
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-formula", async (req: ProveFormulaRequest): Promise<boolean> => {
            // check if proofExplorer is already open with another proof
            if (this.proofExplorer?.proofIsDirty()) {
                // ask if the proof needs to be saved
                const yesNoCancel: YesNoCancel = await this.proofExplorer?.queryQuitProofAndSave();
                if (yesNoCancel === "cancel") {
                    return false;
                }
            }
            this.proofExplorer.resetView();
            this.proofExplorer.enableView();
            this.proofMate.enableView();
            const success: boolean = await this.xterm.onStartProverRequest(req);
            if (!success) {
                this.proofExplorer.disposeView();
                this.proofMate.disposeView();
            }
            return success;
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.status-proofchain", async (req: PvsFormula) => {
            if (req && req.theoryName && req.formulaName && req.fileName && req.fileExtension) {
                await this.workspaceExplorer.statusProofChain(req);
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.show-proof-summary", async (resource: TheoryItem | { path: string }) => {
            const desc: PvsTheory = await vscodeUtils.getPvsTheory(resource);
            if (desc && desc.theoryName) {
                await this.workspaceExplorer.showProofSummary(desc);
            }
        }));
        // vscode-pvs.prove-theory
        // the sequence of events triggered by this command is:
        // 1. vscodePvsTerminal.startProverSession(desc)
        // 2. vscodePvsTerminal.sendRequest(serverCommand.proveFormula, desc)
        // 3. pvsLanguageServer.proveFormulaRequest(desc)
        //      3.1 typecheck
        //      3.2 loadProofDescriptor
        //      3.3 proveFormula
        // <loop over all theorems>
        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-theory-inline", async (resource: TheoryItem | { path: string }) => {
            commands.executeCommand("vscode-pvs.prove-theory", resource);
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.jprove-theory", async (resource: TheoryItem | { path: string }) => {
            commands.executeCommand("vscode-pvs.prove-theory", resource, { useJprf: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-theory", async (
            resource: TheoryItem | { path: string, theoryName?: string } | string,
            opt?: { useJprf?: boolean, unprovedOnly?: boolean, force?: boolean, cancellationToken?: CancellationToken, origin?: string }
        ) => {
            resource = await this.resolveActiveResource(resource, { save: true });
            const desc: PvsTheory = await vscodeUtils.getPvsTheory(resource);
            if (desc && desc.theoryName) {
                opt = opt || {};
                // ask the user confirmation before restarting pvs
                const yesno: string[] = [ "Yes", "Unproved Only", "No" ];
                const msg: string = opt.useJprf ? `Re-run J-PRF proofs in theory ${desc.theoryName}?` : `Re-run all proofs in theory ${desc.theoryName}?`;
                const ans: string = opt.force ? (opt.unprovedOnly ? yesno[1] : yesno[0]) : await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0], yesno[1]);
                if (ans === yesno[0] || ans === yesno[1]) {
                    opt.unprovedOnly = ans === yesno[1];
                    const progressMsg: string = (opt.unprovedOnly) ?
                        opt.useJprf ? `Running unproved J-PRF proofs (theory ${desc.theoryName})` : `Running unproved proofs in theory ${desc.theoryName}`
                            : opt.useJprf ? `Re-running J-PRF proofs (theory ${desc.theoryName})` : `Re-running proofs in theory ${desc.theoryName}`;
                    return await this.executeTheoryProof(desc, {
                        tccsOnly: false,
                        useJprf: opt.useJprf,
                        unprovedOnly: opt.unprovedOnly,
                        progressMsg,
                        cancellationToken: opt.cancellationToken
                    });
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: vscode-pvs.prove-theory invoked with null resource", resource);
            }
            return null;
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.jprove-importchain", async (resource: TheoryItem | { path: string }) => {
            commands.executeCommand("vscode-pvs.prove-importchain", resource, { useJprf: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-importchain", async (resource: TheoryItem | { path: string }, opt?: { useJprf?: boolean }) => {
            const desc: PvsTheory = await vscodeUtils.getPvsTheory(resource);
            if (desc && desc.theoryName) {
                opt = opt || {};
                // ask the user confirmation before restarting pvs
                const yesno: string[] = [ "Yes", "No" ];
                const msg: string = opt.useJprf ? `Re-run J-PRF importchain for theory ${desc.theoryName}?` : `Re-run importchain for theory ${desc.theoryName}?`;
                const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0])
                if (ans === yesno[0]) {
                    this.quietMode = true;
                    this.proofMate.disableView();
                    this.proofExplorer.disableView();
                    this.xterm.bye();

                    const msg: string = opt.useJprf ? `Re-running J-PRF importchain for theory ${desc.theoryName}` : `Re-running importchain for theory ${desc.theoryName}`
                    this.statusBar.showProgress(msg);

                    try{
                        await this.workspaceExplorer.proveImportChainWithProgress(desc, opt);
                        this.statusBar.ready();
                        this.quietMode = false;
                    } catch { }
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: vscode-pvs.prove-importchain invoked with null resource", resource);
            }
        }));
        // this request comes from the context menu displayed by the editor
        context.subscriptions.push(this.registerCommand("vscode-pvs.discharge-tccs", async (
            resource: FormulaItem | TheoryItem | { path: string, theoryName?: string } | string,
            opt?: { useJprf?: boolean, unprovedOnly?: boolean, force?: boolean, formulaName?: string, match?: RegExp }
        ) => {
            resource = await this.resolveActiveResource(resource, { save: true });

            const desc: PvsTheory = await vscodeUtils.getPvsTheory(resource);
            if (desc?.theoryName) {
                opt = opt || {};
                // ask the user confirmation before discharging
                const msg: string = opt.useJprf ? `Discharge TCCs using J-PRF?` : `Discharge all TCCs?`;
                const yesno: string[] = [ "Yes", "Unproved Only", "No" ];
                const ans: string = opt.force ? (opt.unprovedOnly ? yesno[1] : yesno[0]) : await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0], yesno[1]);
                if (ans === yesno[0] || ans === yesno[1]) {
                    opt.unprovedOnly = ans === yesno[1];
                    const progressMsg: string = (opt.unprovedOnly) ?
                        opt.useJprf ? `Running unproved J-PRF TCCs (theory ${desc.theoryName})` : `Running unproved TCCs in theory ${desc.theoryName}`
                            : opt.useJprf ? `Re-running J-PRF TCCs (theory ${desc.theoryName})` : `Re-running TCCs in theory ${desc.theoryName}`;
                    return await this.executeDischargeTccs(desc, {
                        useJprf: opt.useJprf,
                        unprovedOnly: opt.unprovedOnly,
                        match: opt.match || (opt.formulaName ? new RegExp(`${opt.formulaName}_TCC`, "g") : null),
                        progressMsg
                    });
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: vscode-pvs.discharge-tccs invoked with null resource", resource);
            }
            return null;
        }));
        // this request comes from the codelens in the .tccs file
        context.subscriptions.push(this.registerCommand("vscode-pvs.discharge-matching-tccs", async (
            resource: PvsFormula | { path: string },
            opt?: { useJprf?: boolean, unprovedOnly?: boolean, force?: boolean }
        ) => {
            resource = await this.resolveActiveResource(resource, { save: true });
            const desc: PvsTheory = await vscodeUtils.getPvsTheory(resource);
            const formulaName: string = (<{ formulaName: string }>resource)["formulaName"]?.split("_TCC")[0];
            if (desc?.theoryName && formulaName) {
                opt = opt || {};
                // ask the user confirmation before discharging
                const yesno: string[] = [ `Match ${formulaName}`, "All TCCs", "No" ];
                const msg: string = opt.useJprf ? `Discharge TCCs using J-PRF?` : `Discharge TCCs?`;
                const ans: string = opt.force ? yesno[0] : await vscode.window.showInformationMessage(msg, { modal: true, detail: "Press 'Esc' to Cancel" }, yesno[0], yesno[1]);
                if (ans === yesno[0] || ans === yesno[1]) {
                    const allTccs: boolean = ans === yesno[1];
                    const progressMsg: string = (opt.unprovedOnly) ?
                        opt.useJprf ? `Running unproved ${allTccs ? "" : formulaName + " "}J-PRF TCCs (theory ${desc.theoryName})` : `Running unproved ${allTccs ? "" : formulaName + " "} TCCs in theory ${desc.theoryName}`
                            : opt.useJprf ? `Re-running ${allTccs ? "" : formulaName + " "}J-PRF TCCs (theory ${desc.theoryName})` : `Re-running ${allTccs ? "" : formulaName + " "}TCCs in theory ${desc.theoryName}`;
                    return await this.executeDischargeTccs(desc, {
                        useJprf: opt.useJprf,
                        unprovedOnly: opt.unprovedOnly,
                        match: formulaName && !allTccs ? new RegExp(`${formulaName}_TCC`, "g") : null,
                        progressMsg
                    });
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: vscode-pvs.discharge-matching-tccs invoked with null resource", resource);
            }
            return null;
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.jdischarge-tccs", async (resource: TheoryItem | { path: string }) => {
            return await commands.executeCommand("vscode-pvs.discharge-tccs", resource, { useJprf: true });
        }));
        // this request comes from workspace explorer
        context.subscriptions.push(this.registerCommand("vscode-pvs.discharge-tccs-explorer", async (resource: TccsOverviewItem) => {
            return await commands.executeCommand("vscode-pvs.discharge-tccs", resource);
        }));

        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-workspace-inline", async (resource: WorkspaceOverviewItem | { path: string }) => {
            commands.executeCommand("vscode-pvs.prove-workspace", resource);
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.jprove-workspace", async (resource: WorkspaceOverviewItem | { path: string }) => {
            commands.executeCommand("vscode-pvs.prove-workspace", resource, { useJprf: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.prove-workspace", async (resource: WorkspaceOverviewItem | { path: string }, opt?: { useJprf?: boolean, unprovedOnly?: boolean }) => {
            resource = await this.resolveActiveResource(resource, { save: true });

            const desc: ContextFolder = await vscodeUtils.getPvsWorkspace(resource);
            if (desc && desc.contextFolder) {
                opt = opt || {};
                // ask the user confirmation before discharging
                const yesno: string[] = [ "Yes", "Unproved Only", "No" ];
                const contextFolderName: string = fsUtils.getContextFolderName(desc.contextFolder);
                const msg: string = opt.useJprf ? `Re-run J-PRF proofs in workspace ${contextFolderName}?` : `Re-run all proofs in workspace ${contextFolderName}?`;
                const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0], yesno[1]);
                if (ans === yesno[0] || ans === yesno[1]) {
                    opt.unprovedOnly = ans === yesno[1];
                    this.quietMode = true;
                    this.proofMate.disableView();
                    this.proofExplorer.disableView();
                    this.xterm.bye();

                    try {
                        await this.workspaceExplorer.proveWorkspaceWithProgress(desc, opt);
                        this.statusBar.ready();
                        this.quietMode = false;
                    } catch {

                    }
                }
            } else {
                this.logError("[vscode-events-dispatcher] Error: vscode-pvs.prove-workspace invoked with null resource", resource);
            }
        }));

        context.subscriptions.push(this.registerCommand("vscode-pvs.clean-bin", async () => {
            // ask the user confirmation before deleting bin files
			const yesno: string[] = [ "Yes", "No" ];
			const msg: string = `Delete pvsbin folder?\n\nThis action can resolve situations where pvs fails to start or execute proof commands.`;
			const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0])
			if (ans === yesno[0]) {
                if (vscode.workspace?.workspaceFolders?.length) {
                    const currentContext: string = vscode.workspace.workspaceFolders[0].uri.path;
                    if (currentContext) {
                        await fsUtils.cleanBin(currentContext, { removePvsbinFolder: true, keepTccs: true, recursive: fsUtils.MAX_RECURSION });
                    }
                }
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.clean-tccs", async () => {
            // ask the user confirmation before deleting bin files
			const yesno: string[] = [ "Yes", "No" ];
			const msg: string = `Delete .tccs files?`;
			const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0])
			if (ans === yesno[0]) {
                if (vscode.workspace?.workspaceFolders?.length) {
                    const currentContext: string = vscode.workspace.workspaceFolders[0].uri?.path;
                    if (currentContext) {
                        await fsUtils.cleanTccs(currentContext, { recursive: fsUtils.MAX_RECURSION });
                        // request context descriptor, so pvs explorer can refresh the view
                        const activeEditor: vscode.TextEditor = vscodeUtils.getActivePvsEditor();
                        if (activeEditor?.document?.fileName) {
                            const desc: FileDescriptor = fsUtils.fname2desc(activeEditor.document.fileName);
                            this.client.sendRequest(serverRequest.getContextDescriptor, { contextFolder: desc.contextFolder });
                        }
                    }
                }
            }
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.x-show-proof", async () => {
            commands.executeCommand("proof-explorer.show-proof");
            // this.proofExplorer?.showWebView({ recenter: true });
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.x-prove", async () => {
            commands.executeCommand("vscode-pvs.prove-formula-at-cursor-position");
            // commands.executeCommand("vscode-pvs.x-show-proof");
        }));
        context.subscriptions.push(this.registerCommand("vscode-pvs.clean-all", async () => {
            // ask the user confirmation before deleting bin files
			const yesno: string[] = [ "Yes", "No" ];
			const msg: string = `Delete temporary files (.tccs and pvsbin) created by PVS?`;
			const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0])
			if (ans === yesno[0]) {
                if (vscode.workspace?.workspaceFolders?.length) {
                    const currentContext: string = vscode.workspace.workspaceFolders[0].uri.path;
                    if (currentContext) {
                        await fsUtils.cleanBin(currentContext, { removePvsbinFolder: true, keepTccs: false, recursive: fsUtils.MAX_RECURSION });
                    }
                }
            }
        }));
        // vscode-pvs.typecheck-file
		context.subscriptions.push(this.registerCommand("vscode-pvs.typecheck-file", async (resource: string | { path: string } | { contextValue: string } | PvsFile | TypeCheckFileRequest) => {
            resource = await this.resolveActiveResource(resource, { save: true });
			if (resource) {
                const requestParam: TypeCheckFileRequest = {
                    file: vscodeUtils.resource2fileDescriptor
                ((typeof resource === 'string'? (<string>resource) : 'file' in resource ?(<TypeCheckFileRequest>resource).file : resource)),
                    force: ((typeof resource !== 'string' && 'force' in resource ?(<TypeCheckFileRequest>resource).force : false))
                }

                if (isPvsFile(requestParam.file)) {
                    // show output panel for feedback
                    // commands.executeCommand("workbench.action.output.toggleOutput", true);
                    // send typecheck request to pvs-server
                    this.client.sendRequest(serverRequest.typecheckFile, requestParam);
                } else {
                    showWarningMessage (`Typechecking can only be performed on .pvs files.`);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));
        // alias for vscode-pvs.typecheck-file
        context.subscriptions.push(this.registerCommand("vscode-pvs.typecheck-file-inline", async (resource: string | { path: string } | { contextValue: string }) => {
            commands.executeCommand("vscode-pvs.typecheck-file", resource);
        }));

        // vscode-pvs.dump-pvs-files
		context.subscriptions.push(this.registerCommand("vscode-pvs.dump-pvs-files", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                const pvsFile: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (isPvsFile(pvsFile)) {
                    const req: DumpPvsFilesRequest = { pvsFile };
                    // send dump-pvs-files request to pvs-server
                    const task: RunningTask = vscodeUtils.runningTask(`Creating dump file for ${pvsFile.fileName}${pvsFile.fileExtension}, please wait...`);
                    this.client.sendRequest(serverRequest.dumpPvsFiles, req);
                    this.client.onNotification(serverRequest.dumpPvsFiles, (ans: DumpPvsFilesResponse) => {
                        task?.resolve();
                        if (ans?.res) {
                            const dmpFile: string = `${ans.res.dmpFile.fileName}${ans.res.dmpFile.fileExtension}`;
                            const msg: string = `Done! ${ans.res.files.length} pvs files stored in ${dmpFile}`;
                            vscodeUtils.showStatusBarMessage(msg);
                            vscodeUtils.showInformationMessageWithOpenFile(msg, ans.res.dmpFile, {
                                openFileButton: `Open ${dmpFile}`
                            });
                        } else {
                            vscodeUtils.showWarningMessage(`Unable to dump file (${ans?.error})`);
                        }
                    });
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));
        // vscode-pvs.undump-pvs-files
		context.subscriptions.push(this.registerCommand("vscode-pvs.undump-pvs-files", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                const dmpFile: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (isDumpFile(dmpFile)) {
                    // ask the user confirmation before undumping
                    const yesno: string[] = [ "Yes", "No" ];
                    const folder: string = getUndumpFolderName(dmpFile);
                    const msg: string = `Undump pvs files to folder '${folder}'?`;
                    const ans: string = await vscode.window.showInformationMessage(msg, { modal: true }, yesno[0]);
                    if (ans === yesno[0]) {
                        const req: UndumpPvsFilesRequest = { dmpFile };
                        // send dump-pvs-files request to pvs-server
                        const task: RunningTask = vscodeUtils.runningTask(`Restoring PVS files from ${dmpFile.fileName}${dmpFile.fileExtension}, please wait...`);
                        this.client.sendRequest(serverRequest.undumpPvsFiles, req);
                        this.client.onNotification(serverRequest.undumpPvsFiles, (ans: UndumpPvsFilesResponse) => {
                            task?.resolve();
                            if (ans?.res?.folder && ans?.res?.files?.length) {
                                const msg: string = `${ans.res.files.length} files undumped successfully!`;
                                vscodeUtils.showStatusBarMessage(msg);
                                vscodeUtils.showInformationMessageWithOpenFile(msg, ans.res.files[ans.res.files.length - 1], {
                                    openFileButton: `Open folder ${folder}`
                                });
                            } else {
                                vscodeUtils.showWarningMessage(`Unable to restore files (${ans?.error})`);
                            }
                        });
                    }
                } else {
                    vscodeUtils.showWarningMessage(`Undump can only be performed on .dmp files`);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));

        // vscode-pvs.show-tccs
		context.subscriptions.push(this.registerCommand("vscode-pvs.show-tccs", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                const desc: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (desc) {
                    // send show-tccs request to pvs-server
                    this.client.sendRequest(serverRequest.showTccs, desc);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));
        // alias for vscode-pvs.show-tccs
		context.subscriptions.push(this.registerCommand("vscode-pvs.show-tccs-alt", async (resource: string | { path: string } | { contextValue: string }) => {
            commands.executeCommand("vscode-pvs.show-tccs", resource);
        }));
        // vscode-pvs.generate-tccs
		context.subscriptions.push(this.registerCommand("vscode-pvs.generate-tccs", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                const desc: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (desc) {
                    // send generate-tccs request to pvs-server
                    this.client.sendRequest(serverRequest.generateTccs, desc);
                    // register handler for response
                    this.client.onNotification(serverRequest.generateTccs, (desc: {
                        response: PvsContextDescriptor,
                        args: {
                            fileName: string,
                            fileExtension: string,
                            contextFolder: string
                        }
                    }) => {
                        if (this.workspaceExplorer && desc?.response) {
                            this.workspaceExplorer.updateContextFolder(desc.response, { tccDescriptor: true, theoriesFromActiveFile: this.showTheoriesFromActiveFile });
                        }
                    });
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));

        // vscode-pvs.parse-file
		context.subscriptions.push(this.registerCommand("vscode-pvs.parse-file", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                const desc: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (desc) {
                    // send parse request to pvs-server
                    this.client.sendRequest(serverRequest.parseFileWithFeedback, desc);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));

        // vscode-pvs.parse-workspace
		context.subscriptions.push(this.registerCommand("vscode-pvs.parse-workspace", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                let desc = vscodeUtils.resource2fileDescriptor(resource);
                if (desc) {
                    // send parse request to pvs-server
                    this.client.sendRequest(serverRequest.parseWorkspaceWithFeedback, desc);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
		}));

        // vscode-pvs.typecheck-workspace
        context.subscriptions.push(this.registerCommand("vscode-pvs.typecheck-workspace-inline", async (resource: string | { path: string } | { contextValue: string }) => {
            commands.executeCommand("vscode-pvs.typecheck-workspace", resource);
        }));
		context.subscriptions.push(this.registerCommand("vscode-pvs.typecheck-workspace", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                let desc = vscodeUtils.resource2fileDescriptor(resource);
                if (desc) {
                    // send parse request to pvs-server
                    this.client.sendRequest(serverRequest.typecheckWorkspaceWithFeedback, desc);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));

        // vscode-pvs.hp2pvs
		context.subscriptions.push(this.registerCommand("vscode-pvs.hp2pvs", async (resource: string | { path: string } | { contextValue: string }) => {
            resource = await this.resolveActiveResource(resource);
			if (resource) {
                let desc = vscodeUtils.resource2fileDescriptor(resource);
                if (desc) {
                    // send parse request to pvs-server
                    this.client.sendRequest(serverRequest.hp2pvs, desc);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
		}));

        // vscode-pvs.latex-file
		context.subscriptions.push(this.registerCommand("vscode-pvs.latex-file", async (resource: string | { path: string } | { contextValue: string } | PvsFile) => {
            resource = await this.resolveActiveResource(resource, { save: true });
			if (resource) {
                const desc: FileDescriptor = vscodeUtils.resource2fileDescriptor(resource);
                if (isPvsFile(desc)) {
                    // send request to pvs-server
                    this.client.sendRequest(serverRequest.latexFile, desc);
                } else {
                    showWarningMessage (`Tried to latexify a non 'pvs' file.`);
                }
            } else {
                this.logError("[vscode-events-dispatcher] Warning: resource is null", resource);
            }
        }));
        // vscode-pvs.latex-theory
        context.subscriptions.push(this.registerCommand("vscode-pvs.latex-theory", async (resource: string | { path: string } | { contextValue: string } | PvsFile) => {
            await this.sendActiveEditorLatexRequest(serverRequest.latexTheory, resource);
        }));
        // vscode-pvs.latex-importchain
        context.subscriptions.push(this.registerCommand("vscode-pvs.latex-importchain", async (resource: string | { path: string } | { contextValue: string } | PvsFile) => {
            await this.sendActiveEditorLatexRequest(serverRequest.latexImportchain, resource);
        }));

        //----------------------------------
        // events triggered by pvs-language-server
        //----------------------------------
        this.client.onNotification("server.status.error", (desc: { msg: string }) => {
            if (desc && desc.msg) {
                vscodeUtils.showErrorMessage(desc.msg);
            }
        });
        this.client.onNotification("server.status.progress", (desc: { msg: string }) => {
            if (desc && desc.msg) {
                this.statusBar.showProgress(desc.msg);
            }
        });
        this.client.onNotification("server.status.warning", (desc?: { msg?: string }) => {
            this.statusBar.clear();
            if (desc && desc.msg) {
                vscodeUtils.showWarningMessage(desc.msg);
            }
        });
        this.client.onNotification("server.status.info", (desc?: { msg?: string }) => {
            this.statusBar.clear();
            if (desc && desc.msg) {
                vscodeUtils.showInformationMessage(desc.msg);
            }
        });
        this.client.onNotification("server.status.start-important-task",
            (desc: { id: string, msg: string, increment?: number
                     taskName?: string, affectedObject?: string }) => {
            if (desc && desc.msg) {
                if (this.quietMode) {
                    this.client.onNotification(`server.status.end-important-task-${desc.id}-with-errors`, (desc: { msg: string }) => {
                        this.statusBar.clear();
                        if (desc && desc.msg) {
                            this.statusBar.showError(desc.msg); // use the status bar rather than dialogs, because we don't have APIs to close old dialogs with potentially stale information
                            vscodeUtils.showErrorMessage(desc.msg);
                            vscodeUtils.showProblemsPanel();
                        }
                    });
                    return;
                }

                // show dialog with progress
                window.withProgress({
                    location: ProgressLocation.Notification,
                    cancellable: false // @M3 #TODO disabled cancellable until a way to cancel operations via web-socket communication is established
                }, (progress, token) => {
                    let complete: boolean = false;
                    // show initial dialog with spinning progress
                    progress.report({ increment: -1, message: desc.msg });
                    // @M3 #TODO I don't think this is needed anymore, now that we have more feedback form the type checker
                    // setTimeout(() => {
                    //     if (!complete) {
                    //         progress.report({
                    //             increment: isNaN(desc.increment) ? -1 : desc.increment,
                    //             message: "Working, please wait... \n(" + desc.msg + ")"
                    //         });
                    //     }
                    // }, 8000);
                    // update the dialog
                    return new Promise<void>((resolve, reject) => {
                        token.onCancellationRequested(() => {
                            if (!complete) {
                                complete = true;
                                // send cancellation request to the server
                                this.client.sendRequest(serverRequest.cancelOperation);
                                // clear status bar
                                this.statusBar.clear();
                                // dispose of the dialog
                                resolve(null);
                            }
                        });
                        this.client.onNotification(`server.status.progress-important-task-${desc.id}`, (desc: { msg: string, increment?: number }) => {
                            let msg: string = desc.msg;
                            if (desc) {
                                // shorten message
                                msg = msg.replace(/ in [\d\.]+ ?s.*$/, "");
                                this.statusBar.showProgress(msg.replace(vscodeUtils.getRootPath(), "\$(workspace-trusted)"), desc.msg);
                                progress.report({
                                    increment: isNaN(desc.increment) ? -1 : desc.increment,
                                    message: msg.replace(vscodeUtils.getRootPath(), "...")
                                });
                                // @M3 #TODO Add an specific log panel to show verbose PVS feedback?
                             }
                        });
                        this.client.onNotification(`server.status.end-important-task-${desc.id}`, (desc: { msg?: string }) => {
                            this.statusBar.ready();
                            complete = true;
                            if (desc && desc.msg) {
                                this.statusBar.showMsg(desc.msg);
                                this.statusBar.ready();
                                vscodeUtils.showInformationMessage(desc.msg);
                                resolve();
                                // progress.report({
                                //     increment: 100,
                                //     message: desc.msg
                                // });
                                // setTimeout(() => {
                                //     resolve(null);
                                // }, this.NOTIFICATION_TIMEOUT);
                                // window.showInformationMessage(desc.msg); // notification is given with the same dialog instead of creating a new one, this avoids cluttering vscode notification list
                            } else {
                                resolve();
                            }
                        });
                        this.client.onNotification(`server.status.end-important-task-${desc.id}-with-errors`, (desc: { msg: string, showProblemsPanel: boolean }) => {
                            this.statusBar.ready();
                            complete = true;
                            if (desc && desc.msg) {
                                this.statusBar.showError(desc.msg);
                                // NOTE: we don't have APIs to close old error dialogs that contain stale information.
                                // The user will need to close the error dialog.
                                // If the user doesn't close the dialog, the message may show up later, and bring confusion.
                                // vscodeUtils.showErrorMessage(desc.msg);
                                vscodeUtils.showErrorMessage("Error: " + desc.msg);
                                // progress.report({
                                //     increment: 100,
                                //     message: "Error: " + desc.msg
                                // });
                                // setTimeout(() => {
                                //     resolve();
                                // }, this.NOTIFICATION_TIMEOUT * 4);
                                if(desc.showProblemsPanel)
                                    vscodeUtils.showProblemsPanel();
                                resolve();
                            } else {
                                resolve();
                            }
                        });
                        this.client.onNotification(`server.status.restart-server`, (desc: { msg?: string }) => {
                            resolve();
                        });
                    });
                });

                // show progress on the status bar
                let usrMsg: string = desc.msg;
                this.statusBar.showProgress(usrMsg.replace(vscodeUtils.getRootPath(), "\$(workspace-trusted)"));
            }
        });

        this.client.onNotification("pvs-error", (msg: string) => {
            if (msg) {
                this.logger.logEvent({
                    actor: "server",
                    source: "eventsDispatcher",
                    event: "server.notification",
                    action: "pvs-error",
                    level: "error",
                    message: msg
                });
                vscodeUtils.showErrorMessage(msg);
            }
        });

        this.pvsFailureHandlers.push((opt?: { msg?: string, fname?: string, method?: string, error_type?: string, src: string, log?: string }) => {
            const src: string = opt.src || "pvs";
            let msg: string = opt.msg || "";
            msg = msg.replace("[pvs-server]", "").trim();
            if (opt.error_type === "dependency") {
                vscodeUtils.showDependencyError(msg);
            } else {
                msg = msg || `pvs-server crashed into Lisp.\nTo continue, you may need to Reboot pvs.`;
                if (opt.fname) {
                    // msg += `\nThe error occurred while processing file [${opt.fname}](file://${opt.fname})`; // vscode is unable to render marked strings in dialogs
                    msg += `\nThe error occurred while processing file ${opt.fname} ${opt?.method}`;
                } else if (opt.method) {
                    // msg += `\nThe error occurred while executing method [${opt.method}](${opt.method})`; // vscode is unable to render marked strings in dialogs
                    msg += `\nThe error occurred while executing the following method ${opt.method}`;
                }
                // vscodeUtils.showCriticalErrorMessage("PVS failed. Please restart using M-x reboot-pvs.");
                vscodeUtils.showFailure(msg, src, opt.log);
            }
        });

        this.client.onNotification("server.status.pvs-failure", (params) => {
            this.logger.logEvent({
                actor: "server",
                source: "eventsDispatcher",
                event: "server.notification",
                action: "server.status.pvs-failure",
                level: "error",
                data: this.sanitizeLogValue(params)
            });
            if (this.workspaceExplorer.pvsFailureHandler) this.workspaceExplorer.pvsFailureHandler(params);
            for(const handler of this.pvsFailureHandlers){ handler(params)};
        });
    }
}