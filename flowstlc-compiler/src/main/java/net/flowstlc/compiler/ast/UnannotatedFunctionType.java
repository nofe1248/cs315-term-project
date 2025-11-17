package net.flowstlc.compiler.ast;

public final class UnannotatedFunctionType implements Type {
    private final Type from;
    private final Type to;

    public UnannotatedFunctionType(Type from, Type to) {
        this.from = from;
        this.to = to;
    }

    public Type getFrom() {
        return from;
    }

    public Type getTo() {
        return to;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitUnannotatedFunctionType(this);
    }
}