package net.flowstlc.compiler.ast;

public final class UnitLiteralExpr implements LiteralExpr {
    private final SourceSpan span;

    public UnitLiteralExpr(SourceSpan span) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
    }

    public UnitLiteralExpr() {
        this(SourceSpan.UNKNOWN);
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitUnitLiteralExpr(this);
    }
}