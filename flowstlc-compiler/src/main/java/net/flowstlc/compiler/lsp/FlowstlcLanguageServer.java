package net.flowstlc.compiler.lsp;

import org.eclipse.lsp4j.InitializeParams;
import org.eclipse.lsp4j.InitializeResult;
import org.eclipse.lsp4j.ServerCapabilities;
import org.eclipse.lsp4j.TextDocumentSyncKind;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.LanguageClientAware;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;
import org.eclipse.lsp4j.SemanticTokensWithRegistrationOptions;

import java.util.concurrent.CompletableFuture;

public final class FlowstlcLanguageServer implements LanguageServer, LanguageClientAware {
    private final FlowstlcTextDocumentService textDocumentService = new FlowstlcTextDocumentService(this);
    private final FlowstlcWorkspaceService workspaceService = new FlowstlcWorkspaceService();

    private volatile LanguageClient client;
    private int shutdown = 1;

    LanguageClient getClient() {
        return client;
    }

    @Override
    public void connect(LanguageClient client) {
        this.client = client;
        this.textDocumentService.connect(client);
    }

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        ServerCapabilities caps = new ServerCapabilities();
        caps.setTextDocumentSync(TextDocumentSyncKind.Full);
        caps.setHoverProvider(true);

        SemanticTokensWithRegistrationOptions sem = new SemanticTokensWithRegistrationOptions();
        sem.setLegend(FlowstlcSemanticTokens.legend());
        sem.setFull(true);
        caps.setSemanticTokensProvider(sem);

        return CompletableFuture.completedFuture(new InitializeResult(caps));
    }

    @Override
    public CompletableFuture<Object> shutdown() {
        shutdown = 0;
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public void exit() {
        System.exit(shutdown);
    }

    @Override
    public TextDocumentService getTextDocumentService() {
        return textDocumentService;
    }

    @Override
    public WorkspaceService getWorkspaceService() {
        return workspaceService;
    }
}
