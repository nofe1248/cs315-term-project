package net.flowstlc.compiler.ast;

public final class StringLiteralExpr implements LiteralExpr {
    private final SourceSpan span;
    private final String value;

    public StringLiteralExpr(SourceSpan span, String value) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.value = value;
    }

    public StringLiteralExpr(String value) {
        this(SourceSpan.UNKNOWN, value);
    }

    public String getValue() {
        return value;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitStringLiteralExpr(this);
    }
}
