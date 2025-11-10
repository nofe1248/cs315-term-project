package net.flowstlc.compiler.ast;

public final class BuiltinType implements Type {
    private final BuiltinKind kind;

    public BuiltinType(BuiltinKind kind) {
        this.kind = kind;
    }

    public BuiltinKind getKind() {
        return kind;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitBuiltinType(this);
    }
}