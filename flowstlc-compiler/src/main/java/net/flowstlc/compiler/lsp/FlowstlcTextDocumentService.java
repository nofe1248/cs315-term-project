package net.flowstlc.compiler.lsp;

import net.flowstlc.compiler.ASTBuilder;
import net.flowstlc.compiler.FlowSTLCLexer;
import net.flowstlc.compiler.FlowSTLCParser;
import net.flowstlc.compiler.ast.Program;
import net.flowstlc.compiler.typechecker.BidirectionalTypeChecker;
import net.flowstlc.compiler.typechecker.TypeError;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;

public final class FlowstlcTextDocumentService implements TextDocumentService {
    private final FlowstlcLanguageServer server;
    private volatile LanguageClient client;

    private final Map<String, String> documentsByUri = new ConcurrentHashMap<>();

    FlowstlcTextDocumentService(FlowstlcLanguageServer server) {
        this.server = server;
    }

    void connect(LanguageClient client) {
        this.client = client;
    }

    @Override
    public void didOpen(org.eclipse.lsp4j.DidOpenTextDocumentParams params) {
        TextDocumentItem doc = params.getTextDocument();
        documentsByUri.put(doc.getUri(), doc.getText());
        publishDiagnostics(doc.getUri(), doc.getText());
    }

    @Override
    public void didChange(org.eclipse.lsp4j.DidChangeTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        String nextText = applyFullSync(params.getContentChanges());
        documentsByUri.put(uri, nextText);
        publishDiagnostics(uri, nextText);
    }

    @Override
    public void didClose(org.eclipse.lsp4j.DidCloseTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        documentsByUri.remove(uri);
        if (client != null) {
            client.publishDiagnostics(new PublishDiagnosticsParams(uri, Collections.emptyList()));
        }
    }

    @Override
    public void didSave(org.eclipse.lsp4j.DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        String text = Optional.ofNullable(params.getText()).orElse(documentsByUri.get(uri));
        if (text != null) {
            documentsByUri.put(uri, text);
            publishDiagnostics(uri, text);
        }
    }

    @Override
    public CompletableFuture<Hover> hover(HoverParams params) {
        try {
            String uri = params.getTextDocument().getUri();
            String text = documentsByUri.get(uri);
            if (text == null) {
                return CompletableFuture.completedFuture(null);
            }

            int offset = LspPositions.offsetAt(text, params.getPosition());
            String ident = LspPositions.identifierAt(text, offset);
            if (ident == null) {
                return CompletableFuture.completedFuture(null);
            }

            Program program = parseToProgram(text);
            if (program == null) {
                return CompletableFuture.completedFuture(null);
            }

            var type = FlowstlcSymbols.lookupTopLevelType(program, ident);
            if (type == null) {
                return CompletableFuture.completedFuture(null);
            }

            MarkupContent mc = new MarkupContent();
            mc.setKind(MarkupKind.MARKDOWN);
            mc.setValue("```flowstlc\n" + ident + " : " + type + "\n```");

            Hover hover = new Hover();
            hover.setContents(mc);
            return CompletableFuture.completedFuture(hover);
        } catch (Exception e) {
            return CompletableFuture.completedFuture(null);
        }
    }

    @Override
    public CompletableFuture<SemanticTokens> semanticTokensFull(SemanticTokensParams params) {
        try {
            String uri = params.getTextDocument().getUri();
            String text = documentsByUri.get(uri);
            if (text == null) {
                return CompletableFuture.completedFuture(new SemanticTokens(Collections.emptyList()));
            }
            return CompletableFuture.completedFuture(FlowstlcSemanticTokens.full(text));
        } catch (Exception e) {
            return CompletableFuture.completedFuture(new SemanticTokens(Collections.emptyList()));
        }
    }

    private static String applyFullSync(List<TextDocumentContentChangeEvent> changes) {
        if (changes == null || changes.isEmpty()) {
            return "";
        }
        return changes.get(changes.size() - 1).getText();
    }

    private void publishDiagnostics(String uri, String text) {
        if (client == null) {
            return;
        }

        List<Diagnostic> diagnostics = new ArrayList<>();

        diagnostics.addAll(collectParseDiagnostics(text));

        if (diagnostics.isEmpty()) {
            try {
                Program program = parseToProgram(text);
                if (program != null) {
                    new BidirectionalTypeChecker().checkProgram(program, "main", text);
                }
            } catch (TypeError te) {
                Diagnostic d = new Diagnostic();
                d.setSeverity(DiagnosticSeverity.Error);
                d.setMessage(te.formatWithSnippet());
                d.setRange(LspPositions.rangeFromSpan(text, te.getSpan()));
                diagnostics.add(d);
            } catch (Exception e) {
                Diagnostic d = new Diagnostic();
                d.setSeverity(DiagnosticSeverity.Error);
                d.setMessage("Internal error: " + e.getMessage());
                d.setRange(new Range(new Position(0, 0), new Position(0, 1)));
                diagnostics.add(d);
            }
        }

        client.publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics));
    }

    private static List<Diagnostic> collectParseDiagnostics(String text) {
        List<Diagnostic> diags = new ArrayList<>();

        FlowSTLCLexer lexer = new FlowSTLCLexer(CharStreams.fromString(text));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FlowSTLCParser parser = new FlowSTLCParser(tokens);

        parser.removeErrorListeners();
        parser.addErrorListener(new BaseErrorListener() {
            @Override
            public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine,
                                    String msg, RecognitionException e) {
                Diagnostic d = new Diagnostic();
                d.setSeverity(DiagnosticSeverity.Error);
                d.setMessage(msg);

                int l = Math.max(0, line - 1);
                int c = Math.max(0, charPositionInLine);

                int endC = c + 1;
                if (offendingSymbol instanceof Token tok && tok.getStopIndex() >= tok.getStartIndex()) {
                    endC = c + Math.max(1, tok.getStopIndex() - tok.getStartIndex() + 1);
                }

                d.setRange(new Range(new Position(l, c), new Position(l, endC)));
                diags.add(d);
            }
        });

        // Trigger parse.
        parser.program();

        return diags;
    }

    private static Program parseToProgram(String text) {
        FlowSTLCLexer lexer = new FlowSTLCLexer(CharStreams.fromString(text));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FlowSTLCParser parser = new FlowSTLCParser(tokens);
        FlowSTLCParser.ProgramContext tree = parser.program();
        return new ASTBuilder().build(tree);
    }
}
