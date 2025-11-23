package net.flowstlc.compiler.ast;

public class StringLiteralExpr implements LiteralExpr {
    private final String value;

    public StringLiteralExpr(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitStringLiteralExpr(this);
    }
}
