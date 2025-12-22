package net.flowstlc.compiler.ast;

public final class ModalityExpr implements Expr {
    private final SourceSpan span;
    private final Expr inner;

    public ModalityExpr(SourceSpan span, Expr inner) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.inner = inner;
    }

    public ModalityExpr(Expr inner) {
        this(SourceSpan.UNKNOWN, inner);
    }

    public Expr getInner() {
        return inner;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitModalityExpr(this);
    }
}
