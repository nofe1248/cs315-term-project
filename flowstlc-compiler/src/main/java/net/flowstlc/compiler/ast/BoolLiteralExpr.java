package net.flowstlc.compiler.ast;

public final class BoolLiteralExpr implements LiteralExpr {
    private final SourceSpan span;
    private final boolean value;

    public BoolLiteralExpr(SourceSpan span, boolean value) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.value = value;
    }

    public BoolLiteralExpr(boolean value) {
        this(SourceSpan.UNKNOWN, value);
    }

    public boolean getValue() {
        return value;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitBoolLiteralExpr(this);
    }
}
