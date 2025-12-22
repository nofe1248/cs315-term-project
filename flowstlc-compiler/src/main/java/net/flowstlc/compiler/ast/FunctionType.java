package net.flowstlc.compiler.ast;

public final class FunctionType implements Type {
    private final SourceSpan span;
    private final Type from;
    private final SecurityLevel level;
    private final Type to;

    public FunctionType(SourceSpan span, Type from, SecurityLevel level, Type to) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.from = from;
        this.level = level;
        this.to = to;
    }

    public FunctionType(Type from, SecurityLevel level, Type to) {
        this(SourceSpan.UNKNOWN, from, level, to);
    }

    public Type getFrom() {
        return from;
    }

    public SecurityLevel getLevel() {
        return level;
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
        return visitor.visitFunctionType(this);
    }
}