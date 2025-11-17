package net.flowstlc.compiler;

public class TypeError extends RuntimeException {
    public TypeError(String message) {
        super(message);
    }
}