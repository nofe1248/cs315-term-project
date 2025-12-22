package net.flowstlc.compiler.interpreter;

import net.flowstlc.compiler.SourceSnippets;
import net.flowstlc.compiler.ast.ASTNode;
import net.flowstlc.compiler.ast.SourceSpan;

public class RuntimeError extends RuntimeException {
    private final SourceSpan span;
    private final String source;

    public RuntimeError(String msg) {
        this(msg, SourceSpan.UNKNOWN, null);
    }

    public RuntimeError(String msg, ASTNode node, String source) {
        this(msg, node == null ? SourceSpan.UNKNOWN : node.getSpan(), source);
    }

    public RuntimeError(String msg, SourceSpan span, String source) {
        super(msg);
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.source = source;
    }

    public SourceSpan getSpan() {
        return span;
    }

    public String getSource() {
        return source;
    }

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
