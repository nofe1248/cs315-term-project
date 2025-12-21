"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
const vscode = __importStar(require("vscode"));
const node_1 = require("vscode-languageclient/node");
const vscode_jsonrpc_1 = require("vscode-jsonrpc");
let client;
function findLspJarInWorkspace() {
    const folders = vscode.workspace.workspaceFolders;
    if (!folders || folders.length === 0) {
        return undefined;
    }
    const candidateDirs = [];
    for (const folder of folders) {
        const root = folder.uri.fsPath;
        candidateDirs.push(root);
        candidateDirs.push(path.join(root, 'target'));
        candidateDirs.push(path.join(root, 'flowstlc-compiler', 'target'));
    }
    for (const dir of candidateDirs) {
        if (!fs.existsSync(dir)) {
            continue;
        }
        let files;
        try {
            files = fs.readdirSync(dir);
        }
        catch {
            continue;
        }
        const matches = files
            .filter((f) => f.startsWith('flowstlc-compiler-') && f.toLowerCase().endsWith('-lsp.jar'))
            .sort();
        if (matches.length > 0) {
            return path.join(dir, matches[matches.length - 1]);
        }
    }
    return undefined;
}
async function activate(context) {
    const cfg = vscode.workspace.getConfiguration('flowstlc');
    const configuredJarPath = (cfg.get('lspJarPath') || '').trim();
    const javaPath = (cfg.get('javaPath') || 'java').trim();
    const jarPath = configuredJarPath || findLspJarInWorkspace();
    if (!jarPath) {
        vscode.window.showErrorMessage('FlowSTLC LSP: Could not locate the language server jar. Build it with `mvn -DskipTests package` and/or set flowstlc.lspJarPath.');
        return;
    }
    if (!fs.existsSync(jarPath)) {
        vscode.window.showErrorMessage(`FlowSTLC LSP: jar not found at ${jarPath}`);
        return;
    }
    const output = vscode.window.createOutputChannel('FlowSTLC');
    output.appendLine(`Starting FlowSTLC LSP with jar: ${jarPath}`);
    const serverOptions = {
        command: javaPath,
        args: ['-jar', jarPath],
        transport: node_1.TransportKind.stdio,
        options: { env: process.env },
    };
    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'flowstlc' }],
        outputChannel: output,
        traceOutputChannel: output,
    };
    client = new node_1.LanguageClient('flowstlc', 'FlowSTLC Language Server', serverOptions, clientOptions);
    const startPromise = client.start();
    startPromise.then(() => client?.setTrace(vscode_jsonrpc_1.Trace.Verbose));
    context.subscriptions.push({
        dispose: () => {
            client?.stop();
        },
    });
    await startPromise;
}
async function deactivate() {
    if (!client) {
        return;
    }
    await client.stop();
    client = undefined;
}
//# sourceMappingURL=extension.js.map