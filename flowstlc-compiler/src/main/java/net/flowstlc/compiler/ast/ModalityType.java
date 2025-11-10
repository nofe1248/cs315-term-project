package net.flowstlc.compiler.ast;

public class ModalityType implements Type {
    private final Type inner;
    private final SecurityLevel level;

    public ModalityType(Type inner, SecurityLevel level) {
        this.inner = inner;
        this.level = level;
    }

    public Type getInner() {
        return inner;
    }

    public SecurityLevel getLevel() {
        return level;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitModalityType(this);
    }
}
