package net.flowstlc.compiler.interpreter;

public class RuntimeError extends RuntimeException {
    public RuntimeError(String msg) {
        super(msg);
    }
}
