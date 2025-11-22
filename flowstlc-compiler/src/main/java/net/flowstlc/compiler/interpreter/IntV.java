package net.flowstlc.compiler.interpreter;

import java.math.BigInteger;

public final class IntV implements Value {
    private final BigInteger value;

    public IntV(BigInteger value) {
        this.value = value;
    }

    public BigInteger getValue() {
        return value;
    }

    @Override
    public String toString() {
        return value.toString();
    }
}
