package net.flowstlc.compiler.ast;

public final class SequenceExpr implements Expr {
    private final SourceSpan span;
    private final Expr first;
    private final Expr second;

    public SequenceExpr(SourceSpan span, Expr first, Expr second) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.first = first;
        this.second = second;
    }

    public SequenceExpr(Expr first, Expr second) {
        this(SourceSpan.UNKNOWN, first, second);
    }

    public Expr getFirst() {
        return first;
    }

    public Expr getSecond() {
        return second;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitSequenceExpr(this);
    }
}
