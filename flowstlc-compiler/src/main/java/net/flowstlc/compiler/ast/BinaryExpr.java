package net.flowstlc.compiler.ast;

public final class BinaryExpr implements Expr {
    private final SourceSpan span;
    private final Expr left;
    private final BinaryOp op;
    private final Expr right;

    public BinaryExpr(SourceSpan span, Expr left, BinaryOp op, Expr right) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.left = left;
        this.op = op;
        this.right = right;
    }

    public BinaryExpr(Expr left, BinaryOp op, Expr right) {
        this(SourceSpan.UNKNOWN, left, op, right);
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
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitBinaryExpr(this);
    }
}
