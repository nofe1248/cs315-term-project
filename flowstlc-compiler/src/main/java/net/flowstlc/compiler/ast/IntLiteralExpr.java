package net.flowstlc.compiler.ast;

import java.math.BigInteger;

public final class IntLiteralExpr implements LiteralExpr {
    private final SourceSpan span;
    private final BigInteger value;

    public IntLiteralExpr(SourceSpan span, BigInteger value) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.value = value;
    }

    public IntLiteralExpr(BigInteger value) {
        this(SourceSpan.UNKNOWN, value);
    }

    public BigInteger getValue() {
        return value;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIntLiteralExpr(this);
    }
}
