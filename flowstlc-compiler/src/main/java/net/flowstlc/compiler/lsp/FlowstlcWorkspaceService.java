package net.flowstlc.compiler.lsp;

import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.services.WorkspaceService;

public final class FlowstlcWorkspaceService implements WorkspaceService {
    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {
        // no-op
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {
        // no-op
    }
}
