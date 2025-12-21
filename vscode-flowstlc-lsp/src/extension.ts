import * as path from 'path';
import * as fs from 'fs';

import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from 'vscode-languageclient/node';
import { Trace } from 'vscode-jsonrpc';

let client: LanguageClient | undefined;

function findLspJarInWorkspace(): string | undefined {
  const folders = vscode.workspace.workspaceFolders;
  if (!folders || folders.length === 0) {
    return undefined;
  }

  const candidateDirs: string[] = [];
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

    let files: string[];
    try {
      files = fs.readdirSync(dir);
    } catch {
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

export async function activate(context: vscode.ExtensionContext) {
  const cfg = vscode.workspace.getConfiguration('flowstlc');
  const configuredJarPath = (cfg.get<string>('lspJarPath') || '').trim();
  const javaPath = (cfg.get<string>('javaPath') || 'java').trim();

  const jarPath = configuredJarPath || findLspJarInWorkspace();
  if (!jarPath) {
    vscode.window.showErrorMessage(
      'FlowSTLC LSP: Could not locate the language server jar. Build it with `mvn -DskipTests package` and/or set flowstlc.lspJarPath.'
    );
    return;
  }

  if (!fs.existsSync(jarPath)) {
    vscode.window.showErrorMessage(`FlowSTLC LSP: jar not found at ${jarPath}`);
    return;
  }

  const output = vscode.window.createOutputChannel('FlowSTLC');
  output.appendLine(`Starting FlowSTLC LSP with jar: ${jarPath}`);

  const serverOptions: ServerOptions = {
    command: javaPath,
    args: ['-jar', jarPath],
    transport: TransportKind.stdio,
    options: { env: process.env },
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'flowstlc' }],
    outputChannel: output,
    traceOutputChannel: output,
  };

  client = new LanguageClient('flowstlc', 'FlowSTLC Language Server', serverOptions, clientOptions);

  const startPromise = client.start();

  startPromise.then(() => client?.setTrace(Trace.Verbose));

  context.subscriptions.push({
    dispose: () => {
      client?.stop();
    },
  });

  await startPromise;
}

export async function deactivate() {
  if (!client) {
    return;
  }
  await client.stop();
  client = undefined;
}
