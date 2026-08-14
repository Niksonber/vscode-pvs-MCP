import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { EventsDispatcher } from './eventsDispatcher';
import { ProofCommandResponse, ProveFormulaResponse } from './common/serverInterface';

import express from 'express';
import cors from 'cors';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import { z } from 'zod';

export class McpHttpServer {
    private server: any = null;
    private activeFormula: any = null;

    constructor(private eventsDispatcher: EventsDispatcher, ) {}

    public start(port = 23457): void {
        const app = express();
        app.use(express.json());
        app.use(cors());

        const mcpServer = new McpServer({
            name: "vscode-pvs",
            version: "0.0.1"
        });

        mcpServer.registerTool(
            "start_proof",
            {
                description: "Start proof session",
                inputSchema:  z.object({
                    formula_path: z.string().describe("The formula path, in the format 'filepath#formula_name'")
                })
            },
            async ({ formula_path }) => {
                if (!formula_path) {
                    throw new Error("Missing formula_path parameter");
                }

                if (!formula_path.includes('#')) {
                    throw new Error("formula_path must be in the format 'filepath#formula_name'");
                }

                const [filePath, formulaName] = formula_path.split('#');
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

        // Register proof_command tool
         mcpServer.registerTool(
            "apply_proof_command",
            {
                description: "Apply proof command",
                inputSchema: z.object({
                    command: z.string().describe("The proof command to execute (e.g., '(grind)')")
                })
            },
            async ({ command }) => {
                if (!command) {
                    throw new Error("Missing command parameter");
                }

                vscode.window.showInformationMessage(`[MCP] Proof command: ${command}`);

                if (!this.activeFormula) {
                    throw new Error("No active formula. Please run start_proof first.");
                }

                // Set up promise to wait for proofCommandResponse
                const waitForResponse = new Promise<ProofCommandResponse>((resolve) => {
                    const listener = (desc: ProofCommandResponse) => {
                        this.eventsDispatcher.removeProofCommandResponseListener(listener);
                        resolve(desc);
                    };
                    this.eventsDispatcher.addProofCommandResponseListener(listener);
                });

                // Trigger sending the text to the server via xterm so the terminal updates!
                await this.eventsDispatcher.xterm.sendTextToServer(command);

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
                const responsePayload = {
                    result: [
                        {
                            id: this.activeFormula.id,
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

        // Register typecheck_file tool
        mcpServer.registerTool(
            "typecheck_file",
            {
                description: "Typecheck a PVS file",
                inputSchema: z.object({
                    file_path: z.string().describe("The absolute path of the PVS file to typecheck (e.g., '/path/to/theory.pvs')")
                })
            },
            async ({ file_path }) => {
                if (!file_path) {
                    throw new Error("Missing file_path parameter");
                }

                vscode.window.showInformationMessage(`[MCP] Typechecking file: ${path.basename(file_path)}`);

                // Set up a promise to wait for the typecheckFileResponse
                const waitForResponse = new Promise<any>((resolve) => {
                    const listener = (desc: any) => {
                        this.eventsDispatcher.removeTypecheckFileResponseListener(listener);
                        resolve(desc);
                    };
                    this.eventsDispatcher.addTypecheckFileResponseListener(listener);
                });

                // Trigger the VSCode typecheck file command
                await vscode.commands.executeCommand("vscode-pvs.typecheck-file", file_path);

                // Await response from PVS
                const desc = await waitForResponse;

                // Formulate response payload
                const responsePayload = {
                    file: file_path,
                    result: desc?.response?.result || "Typechecking completed"
                };

                return {
                    content: [{ type: "text", text: JSON.stringify(responsePayload) }]
                };
            }
        );

        app.post("/mcp", async (req, res) => {
            try {
                const transport = new StreamableHTTPServerTransport();

                res.on('close', () => {
                    transport.close();
                });

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
            vscode.window.showInformationMessage(`Started MCP on: ${mcpUrl}`);
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
