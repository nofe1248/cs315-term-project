package net.flowstlc.compiler.ast;

public final class SequenceExpr implements Expr {
    private final Expr first;
    private final Expr second;

    public SequenceExpr(Expr first, Expr second) {
        this.first = first;
        this.second = second;
    }

    public Expr getFirst() {
        return first;
    }

    public Expr getSecond() {
        return second;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitSequenceExpr(this);
    }
}

