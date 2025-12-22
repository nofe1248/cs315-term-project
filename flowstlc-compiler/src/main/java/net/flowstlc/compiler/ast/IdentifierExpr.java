package net.flowstlc.compiler.ast;

public final class IdentifierExpr implements Expr {
    private final SourceSpan span;
    private final String name;

    public IdentifierExpr(SourceSpan span, String name) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.name = name;
    }

    public IdentifierExpr(String name) {
        this(SourceSpan.UNKNOWN, name);
    }

    public String getName() {
        return name;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIdentifierExpr(this);
    }
}
