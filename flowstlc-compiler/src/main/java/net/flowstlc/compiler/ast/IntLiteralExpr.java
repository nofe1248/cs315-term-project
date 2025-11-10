package net.flowstlc.compiler.ast;

import java.math.BigInteger;

public final class IntLiteralExpr implements LiteralExpr {
    private final BigInteger value;

    public IntLiteralExpr(BigInteger value) {
        this.value = value;
    }

    public BigInteger getValue() {
        return value;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIntLiteralExpr(this);
    }
}
