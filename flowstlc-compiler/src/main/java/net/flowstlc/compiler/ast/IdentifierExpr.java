package net.flowstlc.compiler.ast;

public final class IdentifierExpr implements Expr {
    private final String name;

    public IdentifierExpr(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIdentifierExpr(this);
    }
}
