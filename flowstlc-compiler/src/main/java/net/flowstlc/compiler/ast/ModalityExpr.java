package net.flowstlc.compiler.ast;

public final class ModalityExpr implements Expr {
    private final Expr inner;

    public ModalityExpr(Expr inner) {
        this.inner = inner;
    }

    public Expr getInner() {
        return inner;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitModalityExpr(this);
    }
}
