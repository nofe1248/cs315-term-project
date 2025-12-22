package net.flowstlc.compiler.ast;

import java.util.List;

public final class Program implements ASTNode {
    private final SourceSpan span;
    private final List<Declaration> declarations;

    public Program(SourceSpan span, List<Declaration> declarations) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.declarations = declarations;
    }

    public Program(List<Declaration> declarations) {
        this(SourceSpan.UNKNOWN, declarations);
    }

    public List<Declaration> getDeclarations() {
        return declarations;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitProgram(this);
    }
}
