package net.flowstlc.compiler.ast;

public final class LetExpr implements Expr {
    private final String name;
    private final Expr bound;
    private final Expr inExpr;

    public LetExpr(String name, Expr bound, Expr inExpr) {
        this.name = name;
        this.bound = bound;
        this.inExpr = inExpr;
    }

    public String getName() {
        return name;
    }

    public Expr getBound() {
        return bound;
    }

    public Expr getInExpr() {
        return inExpr;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitLetExpr(this);
    }
}
