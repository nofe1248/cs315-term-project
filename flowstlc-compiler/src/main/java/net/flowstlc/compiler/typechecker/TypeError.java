package net.flowstlc.compiler.typechecker;

public class TypeError extends RuntimeException {
    public TypeError(String message) {
        super(message);
    }
}