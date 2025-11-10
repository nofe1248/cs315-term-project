package net.flowstlc.compiler.ast;

public final class UnaryExpr implements Expr {
    private final UnaryOp op;
    private final Expr expr;

    public UnaryExpr(UnaryOp op, Expr expr) {
        this.op = op;
        this.expr = expr;
    }

    public UnaryOp getOp() {
        return op;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitUnaryExpr(this);
    }
}
