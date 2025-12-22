package net.flowstlc.compiler.ast;

public final class BuiltinType implements Type {
    private final SourceSpan span;
    private final BuiltinKind kind;

    public BuiltinType(SourceSpan span, BuiltinKind kind) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.kind = kind;
    }

    public BuiltinType(BuiltinKind kind) {
        this(SourceSpan.UNKNOWN, kind);
    }

    public BuiltinKind getKind() {
        return kind;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitBuiltinType(this);
    }
}