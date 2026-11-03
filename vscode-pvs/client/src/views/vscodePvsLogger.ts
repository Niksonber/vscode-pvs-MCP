/**
 * @module vscodePvsLogger
 * @author Paolo Masci
 * @date 2020.07.31
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

import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import * as fsUtils from '../common/fsUtils';

export type PvsLogActor = "user" | "mcp" | "server" | "system";

export interface PvsLogEntry {
    timestamp: string;
    localTimestamp: string;
    sessionId: string;
    actor: PvsLogActor;
    source: string;
    event: string;
    action?: string;
    level?: "info" | "warn" | "error" | "debug";
    message?: string;
    data?: any;
}

export class VSCodePvsLogger {
    protected profiler: vscode.OutputChannel;
    protected readonly logFolder: string;
    protected readonly sessionId: string;

    constructor () {
        this.logFolder = path.join(fsUtils.HOME_DIR, ".pvslog");
        this.sessionId = `session-${Date.now()}-${Math.random().toString(36).substring(2, 8)}`;
        this.ensureLogFolder();
    }

    protected ensureLogFolder (): void {
        try {
            if (!fs.existsSync(this.logFolder)) {
                fs.mkdirSync(this.logFolder, { recursive: true });
            }
        } catch (err) {
            // Avoid crashing extension if home folder is not writable
        }
    }

    public getLogFilePath (): string {
        const now = new Date();
        const yyyy = now.getFullYear();
        const mm = String(now.getMonth() + 1).padStart(2, '0');
        const dd = String(now.getDate()).padStart(2, '0');
        return path.join(this.logFolder, `vscode-pvs-events-${yyyy}-${mm}-${dd}.jsonl`);
    }

    public getSessionId (): string {
        return this.sessionId;
    }

    activate (context: vscode.ExtensionContext): void {
        this.ensureLogFolder();
        this.logEvent({
            actor: "system",
            source: "vscodePvsLogger",
            event: "session.start",
            action: "activate",
            message: `[vscodePvsLogger] Activated JSONL event logger in ${this.getLogFilePath()}`
        });
    }

    public logEvent (entry: Omit<PvsLogEntry, "timestamp" | "localTimestamp" | "sessionId">): void {
        try {
            this.ensureLogFolder();
            const record: PvsLogEntry = {
                timestamp: new Date().toISOString(),
                localTimestamp: fsUtils.generateTimestamp(),
                sessionId: this.sessionId,
                ...entry
            };
            const line = JSON.stringify(record) + "\n";
            fs.appendFileSync(this.getLogFilePath(), line, { encoding: "utf8" });
        } catch (err) {
            // Never disrupt prover/extension workflow on logging error
        }
    }

    public logConsole (
        message: string,
        meta?: Partial<Omit<PvsLogEntry, "timestamp" | "localTimestamp" | "sessionId" | "message">>
    ): void {
        console.log(message);
        this.logEvent({
            actor: meta?.actor || "system",
            source: meta?.source || "eventsDispatcher",
            event: meta?.event || "console.log",
            action: meta?.action,
            message,
            data: meta?.data
        });
    }

    public logError (
        message: string,
        error?: any,
        meta?: Partial<Omit<PvsLogEntry, "timestamp" | "localTimestamp" | "sessionId" | "message">>
    ): void {
        if (error !== undefined) {
            console.error(message, error);
        } else {
            console.error(message);
        }
        const serializedError = error instanceof Error
            ? { name: error.name, message: error.message, stack: error.stack }
            : error;
        this.logEvent({
            actor: meta?.actor || "system",
            source: meta?.source || "eventsDispatcher",
            event: meta?.event || "console.error",
            action: meta?.action,
            message,
            data: meta?.data !== undefined ? { ...meta.data, error: serializedError } : (serializedError !== undefined ? { error: serializedError } : undefined)
        });
    }
    
    profilerData (data: string): void {
        const showProfilerOutput: boolean = vscode.workspace.getConfiguration().get("pvs.xtras.enableProfiler");
        if (showProfilerOutput) {
            if (!this.profiler) {
                this.profiler = vscode.window.createOutputChannel("vscode-pvs:profiler");
                this.profiler.clear();
            }
            this.profiler?.appendLine(data);
        } else {
            this.profiler?.hide();
        }
        this.logEvent({
            actor: "server",
            source: "profiler",
            event: "profiler.data",
            data
        });
    }
}