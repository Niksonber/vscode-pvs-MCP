import * as http from 'http';
import * as url from 'url';
import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { EventsDispatcher } from './eventsDispatcher';
import { ProofCommandResponse, ProveFormulaResponse } from './common/serverInterface';

export class McpHttpServer {
    private server: http.Server | null = null;
    private activeFormula: any = null;

    constructor(private eventsDispatcher: EventsDispatcher) {}

    public start(port = 23457): void {
        this.server = http.createServer((req, res) => {
            // Enable CORS
            res.setHeader('Access-Control-Allow-Origin', '*');
            res.setHeader('Access-Control-Allow-Methods', 'POST, GET, OPTIONS');
            res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

            if (req.method === 'OPTIONS') {
                res.writeHead(200);
                res.end();
                return;
            }

            const parsedUrl = url.parse(req.url || '', true);
            const chunks: any[] = [];

            req.on('data', chunk => chunks.push(chunk));
            req.on('end', async () => {
                const bodyStr = Buffer.concat(chunks).toString();
                let body: any = {};
                try {
                    body = JSON.parse(bodyStr || '{}');
                } catch (err) {
                    // Ignore parse errors for empty/non-JSON bodies
                }

                try {
                    if (parsedUrl.pathname === '/prove-formula' && req.method === 'POST') {
                        const formulaPath = body.formula_path || body.formulaPath;
                        if (!formulaPath) {
                            res.writeHead(400, { 'Content-Type': 'application/json' });
                            res.end(JSON.stringify({ error: "Missing formula_path parameter" }));
                            return;
                        }

                        if (!formulaPath.includes('#')) {
                            res.writeHead(400, { 'Content-Type': 'application/json' });
                            res.end(JSON.stringify({ error: "formula_path must be in the format 'filepath#formula_name'" }));
                            return;
                        }

                        const [filePath, formulaName] = formulaPath.split('#');
                        vscode.window.showInformationMessage(`[MCP] Proving formula '${formulaName}'...`);
                        const fileExtension = path.extname(filePath);
                        const fileName = path.basename(filePath, fileExtension);
                        const contextFolder = path.dirname(filePath);

                        let theoryName = fileName;
                        try {
                            if (fs.existsSync(filePath)) {
                                const content = fs.readFileSync(filePath, 'utf8');
                                const match = content.match(/^\s*([a-zA-Z0-9_]+)\s*:\s*THEORY/m);
                                if (match) {
                                    theoryName = match[1];
                                }
                            }
                        } catch (e) {
                            console.error("[mcp-http-server] Error reading theory file", e);
                        }

                        // Store active formula parameters
                        this.activeFormula = {
                            contextFolder,
                            fileName,
                            fileExtension,
                            theoryName,
                            formulaName,
                            proofFile: {
                                contextFolder,
                                fileName,
                                fileExtension: ".jprf"
                            }
                        };

                        // Set up a promise to wait for the proveFormulaResponse
                        const waitForResponse = new Promise<ProveFormulaResponse>((resolve) => {
                            const listener = (desc: ProveFormulaResponse) => {
                                this.eventsDispatcher.removeProveFormulaResponseListener(listener);
                                resolve(desc);
                            };
                            this.eventsDispatcher.addProveFormulaResponseListener(listener);
                        });

                        // Trigger the VSCode prove command
                        await vscode.commands.executeCommand("vscode-pvs.prove-formula", this.activeFormula);

                        // Await response from PVS
                        const desc = await waitForResponse;

                        // Save proof_id into activeFormula if present
                        let proof_id = "";
                        if (desc && desc.res && typeof desc.res !== 'string') {
                            proof_id = desc.res.id || "";
                        }
                        this.activeFormula.id = proof_id;

                        // Formulate response compatible with raw PVS WS output
                        const responsePayload = [{
                            id: desc?.req?.formulaName || formulaName,
                            result: [
                                {
                                    id: proof_id,
                                    commentary: desc?.res && typeof desc.res !== 'string' 
                                        ? (typeof desc.res.commentary === 'string' ? [desc.res.commentary] : desc.res.commentary)
                                        : ["Proof started"]
                                }
                            ]
                        }];

                        res.writeHead(200, { 'Content-Type': 'application/json' });
                        res.end(JSON.stringify(responsePayload));

                    } else if (parsedUrl.pathname === '/proof-command' && req.method === 'POST') {
                        const command = body.command;
                        if (!command) {
                            res.writeHead(400, { 'Content-Type': 'application/json' });
                            res.end(JSON.stringify({ error: "Missing command parameter" }));
                            return;
                        }

                        vscode.window.showInformationMessage(`[MCP] Proof command: ${command}`);

                        if (!this.activeFormula) {
                            res.writeHead(400, { 'Content-Type': 'application/json' });
                            res.end(JSON.stringify({ error: "No active formula. Please run start_proof (/prove-formula) first." }));
                            return;
                        }

                        const proofCommand = {
                            ...this.activeFormula,
                            cmd: command,
                            origin: "mcp"
                        };

                        // Set up promise to wait for proofCommandResponse
                        const waitForResponse = new Promise<ProofCommandResponse>((resolve) => {
                            const listener = (desc: ProofCommandResponse) => {
                                this.eventsDispatcher.removeProofCommandResponseListener(listener);
                                resolve(desc);
                            };
                            this.eventsDispatcher.addProofCommandResponseListener(listener);
                        });

                        // Trigger the VSCode send proof command
                        await vscode.commands.executeCommand("vscode-pvs.send-proof-command", proofCommand);

                        // Await response from PVS
                        const desc = await waitForResponse;

                        let commentaryList: string[] = [];
                        let statusStr = "";
                        let sequentObj = null;

                        if (desc && desc.res) {
                            if (typeof desc.res === 'string') {
                                commentaryList = [desc.res];
                                statusStr = desc.res;
                            } else {
                                commentaryList = typeof desc.res.commentary === 'string' 
                                    ? [desc.res.commentary] 
                                    : desc.res.commentary;
                                statusStr = desc.res.status || "";
                                sequentObj = desc.res.sequent || null;
                            }
                        }

                        // Formulate response compatible with raw PVS WS output
                        const responsePayload = [{
                            result: [
                                {
                                    id: this.activeFormula.id,
                                    commentary: commentaryList,
                                    status: statusStr,
                                    sequent: sequentObj
                                }
                            ]
                        }];

                        res.writeHead(200, { 'Content-Type': 'application/json' });
                        res.end(JSON.stringify(responsePayload));

                    } else {
                        res.writeHead(404, { 'Content-Type': 'application/json' });
                        res.end(JSON.stringify({ error: "Endpoint not found" }));
                    }
                } catch (err: any) {
                    console.error("[mcp-http-server] Error handling request:", err);
                    res.writeHead(500, { 'Content-Type': 'application/json' });
                    res.end(JSON.stringify({ error: "Internal Server Error", details: err?.message || String(err) }));
                }
            });
        });

        this.server.listen(port, () => {
            console.log(`[mcp-http-server] Integration HTTP server listening on port ${port}`);
        });
    }

    public stop(): void {
        if (this.server) {
            this.server.close();
            this.server = null;
            console.log(`[mcp-http-server] Integration HTTP server stopped.`);
        }
    }
}
