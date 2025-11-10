package net.flowstlc.compiler.ast;

public final class BinaryExpr implements Expr {
    private final Expr left;
    private final BinaryOp op;
    private final Expr right;

    public BinaryExpr(Expr left, BinaryOp op, Expr right) {
        this.left = left;
        this.op = op;
        this.right = right;
    }

    public Expr getLeft() {
        return left;
    }

    public BinaryOp getOp() {
        return op;
    }

    public Expr getRight() {
        return right;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitBinaryExpr(this);
    }
}
