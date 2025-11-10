package net.flowstlc.compiler.ast;

public final class ConstantDeclaration implements Declaration {
    private final String name;
    private final Type type;
    private final Expr value;

    public ConstantDeclaration(String name, Type type, Expr value) {
        this.name = name;
        this.type = type;
        this.value = value;
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
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitConstantDeclaration(this);
    }
}
