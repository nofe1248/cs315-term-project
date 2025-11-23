package net.flowstlc.compiler.interpreter;

public class StringV implements Value {
    private final String value;

    public StringV(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public String toString() {
        return "\"" + value + "\"";
    }
}
