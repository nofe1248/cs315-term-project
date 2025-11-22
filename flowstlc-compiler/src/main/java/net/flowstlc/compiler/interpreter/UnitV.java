package net.flowstlc.compiler.interpreter;

public final class UnitV implements Value {
    public static final UnitV INSTANCE = new UnitV();

    private UnitV() {}

    @Override
    public String toString() {
        return "()";
    }
}
