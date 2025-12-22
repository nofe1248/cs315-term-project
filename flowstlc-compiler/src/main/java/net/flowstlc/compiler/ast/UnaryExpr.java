package net.flowstlc.compiler.ast;

public final class UnaryExpr implements Expr {
    private final SourceSpan span;
    private final UnaryOp op;
    private final Expr expr;

    public UnaryExpr(SourceSpan span, UnaryOp op, Expr expr) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.op = op;
        this.expr = expr;
    }

    public UnaryExpr(UnaryOp op, Expr expr) {
        this(SourceSpan.UNKNOWN, op, expr);
    }

    public UnaryOp getOp() {
        return op;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitUnaryExpr(this);
    }
}
