package net.flowstlc.compiler.interpreter;

public final class BoolV implements Value {
    private final boolean value;

    public BoolV(boolean value) {
        this.value = value;
    }

    public boolean getValue() {
        return value;
    }

    @Override
    public String toString() {
        return Boolean.toString(value);
    }
}
