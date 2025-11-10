package net.flowstlc.compiler.ast;

public final class IfExpr implements Expr {
    private final Expr condition;
    private final Expr thenBranch;
    private final Expr elseBranch;

    public IfExpr(Expr condition, Expr thenBranch, Expr elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    public Expr getCondition() {
        return condition;
    }

    public Expr getThenBranch() {
        return thenBranch;
    }

    public Expr getElseBranch() {
        return elseBranch;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIfExpr(this);
    }
}
