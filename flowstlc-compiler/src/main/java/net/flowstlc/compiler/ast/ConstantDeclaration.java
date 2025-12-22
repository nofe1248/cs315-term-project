package net.flowstlc.compiler.ast;

public final class ConstantDeclaration implements Declaration {
    private final SourceSpan span;
    private final String name;
    private final Type type;
    private final Expr value;

    public ConstantDeclaration(SourceSpan span, String name, Type type, Expr value) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.name = name;
        this.type = type;
        this.value = value;
    }

    public ConstantDeclaration(String name, Type type, Expr value) {
        this(SourceSpan.UNKNOWN, name, type, value);
    }

    public String getName() {
        return name;
    }

    public Type getType() {
        return type;
    }

    public Expr getValue() {
        return value;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitConstantDeclaration(this);
    }
}
