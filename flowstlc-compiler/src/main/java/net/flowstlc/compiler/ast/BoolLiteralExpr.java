package net.flowstlc.compiler.ast;

public final class BoolLiteralExpr implements LiteralExpr {
    private final boolean value;

    public BoolLiteralExpr(boolean value) {
        this.value = value;
    }

    public boolean getValue() {
        return value;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitBoolLiteralExpr(this);
    }
}
