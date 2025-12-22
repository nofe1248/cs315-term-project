package net.flowstlc.compiler.ast;

public final class ModalityType implements Type {
    private final SourceSpan span;
    private final Type inner;
    private final SecurityLevel level;

    public ModalityType(SourceSpan span, Type inner, SecurityLevel level) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.inner = inner;
        this.level = level;
    }

    public ModalityType(Type inner, SecurityLevel level) {
        this(SourceSpan.UNKNOWN, inner, level);
    }

    public Type getInner() {
        return inner;
    }

    public SecurityLevel getLevel() {
        return level;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitModalityType(this);
    }
}
