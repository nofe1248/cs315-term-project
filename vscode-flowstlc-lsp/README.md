# FlowSTLC VS Code LSP Client

This folder contains a minimal VS Code extension that launches the FlowSTLC language server (the shaded `*-lsp.jar`) over stdio.

## Prereqs

- Java 17+
- Node.js (for building the extension)
- The FlowSTLC LSP jar built from `flowstlc-compiler`.

## Build the server jar

From the `flowstlc-compiler` folder:

```powershell
mvn -DskipTests clean package
```

You should get:

- `target/flowstlc-compiler-1.0-SNAPSHOT-lsp.jar`

## Configure the jar path (optional)

If the extension can’t find your jar automatically, set:

- `flowstlc.lspJarPath`

in VS Code settings.

## Build and run the extension

Open this folder (`vscode-flowstlc-lsp`) in VS Code, then:

```powershell
npm install
npm run compile
```

Press **F5** to launch the Extension Development Host.

Open a `.flowstlc` file and you should see diagnostics.

## Troubleshooting

- View the Output panel and pick **FlowSTLC**.
- Ensure `java` is on PATH (or set `flowstlc.javaPath`).

