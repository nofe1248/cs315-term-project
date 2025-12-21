package net.flowstlc.compiler.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;

import java.io.InputStream;
import java.io.OutputStream;

public final class LspMain {
    private LspMain() {
    }

    public static void main(String[] args) {
        FlowstlcLanguageServer server = new FlowstlcLanguageServer();

        InputStream in = System.in;
        OutputStream out = System.out;

        var launcher = LSPLauncher.createServerLauncher(server, in, out);
        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        launcher.startListening();
    }
}
