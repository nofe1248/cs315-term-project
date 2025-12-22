package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.SourceSnippets;
import net.flowstlc.compiler.ast.ASTNode;
import net.flowstlc.compiler.ast.SourceSpan;

public class TypeError extends RuntimeException {
    private final SourceSpan span;
    private final String source;

    public TypeError(String message) {
        this(message, SourceSpan.UNKNOWN, null);
    }

    public TypeError(String message, ASTNode node, String source) {
        this(message, node == null ? SourceSpan.UNKNOWN : node.getSpan(), source);
    }

    public TypeError(String message, SourceSpan span, String source) {
        super(message);
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.source = source;
    }

    public SourceSpan getSpan() {
        return span;
    }

    public String getSource() {
        return source;
    }

    /** Human-friendly message including a snippet if source/span are available. */
    public String formatWithSnippet() {
        if (source == null || span == null || !span.isKnown()) {
            return getMessage();
        }
        String snip = SourceSnippets.snippet(source, span);
        if (snip.isEmpty()) {
            return getMessage();
        }
        return getMessage() + "\n\n" + snip;
    }
}