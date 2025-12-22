package net.flowstlc.compiler.ast;

public final class UnannotatedFunctionType implements Type {
    private final SourceSpan span;
    private final Type from;
    private final Type to;

    public UnannotatedFunctionType(SourceSpan span, Type from, Type to) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.from = from;
        this.to = to;
    }

    public UnannotatedFunctionType(Type from, Type to) {
        this(SourceSpan.UNKNOWN, from, to);
    }

    public Type getFrom() {
        return from;
    }

    public Type getTo() {
        return to;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitUnannotatedFunctionType(this);
    }
}