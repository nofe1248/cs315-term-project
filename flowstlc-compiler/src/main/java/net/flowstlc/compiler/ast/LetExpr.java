package net.flowstlc.compiler.ast;

public final class LetExpr implements Expr {
    private final SourceSpan span;
    private final String name;
    private final Expr bound;
    private final Expr inExpr;

    public LetExpr(SourceSpan span, String name, Expr bound, Expr inExpr) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.name = name;
        this.bound = bound;
        this.inExpr = inExpr;
    }

    public LetExpr(String name, Expr bound, Expr inExpr) {
        this(SourceSpan.UNKNOWN, name, bound, inExpr);
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
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitLetExpr(this);
    }
}
