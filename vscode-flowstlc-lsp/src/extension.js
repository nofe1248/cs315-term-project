"use strict";
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var __generator = (this && this.__generator) || function (thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g = Object.create((typeof Iterator === "function" ? Iterator : Object).prototype);
    return g.next = verb(0), g["throw"] = verb(1), g["return"] = verb(2), typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (g && (g = 0, op[0] && (_ = 0)), _) try {
            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [op[0] & 2, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
var path = require("path");
var fs = require("fs");
var vscode = require("vscode");
var node_1 = require("vscode-languageclient/node");
var client;
function findLspJarInWorkspace() {
    var folders = vscode.workspace.workspaceFolders;
    if (!folders || folders.length === 0) {
        return undefined;
    }
    for (var _i = 0, folders_1 = folders; _i < folders_1.length; _i++) {
        var folder = folders_1[_i];
        var candidateDir = path.join(folder.uri.fsPath);
        if (!fs.existsSync(candidateDir)) {
            continue;
        }
        var files = fs.readdirSync(candidateDir);
        var matches = files
            .filter(function (f) { return f.toLowerCase().endsWith('-lsp.jar') && f.startsWith('flowstlc-compiler-'); })
            .sort();
        if (matches.length > 0) {
            return path.join(candidateDir, matches[matches.length - 1]);
        }
    }
    return undefined;
}
function activate(context) {
    return __awaiter(this, void 0, void 0, function () {
        var cfg, configuredJarPath, javaPath, jarPath, output, serverOptions, clientOptions;
        return __generator(this, function (_a) {
            cfg = vscode.workspace.getConfiguration('flowstlc');
            configuredJarPath = (cfg.get('lspJarPath') || '').trim();
            javaPath = (cfg.get('javaPath') || 'java').trim();
            jarPath = configuredJarPath || findLspJarInWorkspace();
            if (!jarPath) {
                vscode.window.showErrorMessage('FlowSTLC LSP: Could not locate the language server jar. Build it with `mvn -DskipTests package` and/or set flowstlc.lspJarPath.');
                return [2 /*return*/];
            }
            if (!fs.existsSync(jarPath)) {
                vscode.window.showErrorMessage("FlowSTLC LSP: jar not found at ".concat(jarPath));
                return [2 /*return*/];
            }
            output = vscode.window.createOutputChannel('FlowSTLC');
            output.appendLine("Starting FlowSTLC LSP with jar: ".concat(jarPath));
            serverOptions = {
                command: javaPath,
                args: ['-jar', jarPath],
                transport: node_1.TransportKind.stdio,
                options: { env: process.env },
            };
            clientOptions = {
                documentSelector: [{ scheme: 'file', language: 'flowstlc' }],
                outputChannel: output,
            };
            client = new node_1.LanguageClient('flowstlc', 'FlowSTLC Language Server', serverOptions, clientOptions);
            context.subscriptions.push(client.start());
            return [2 /*return*/];
        });
    });
}
function deactivate() {
    return __awaiter(this, void 0, void 0, function () {
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    if (!client) {
                        return [2 /*return*/];
                    }
                    return [4 /*yield*/, client.stop()];
                case 1:
                    _a.sent();
                    client = undefined;
                    return [2 /*return*/];
            }
        });
    });
}
