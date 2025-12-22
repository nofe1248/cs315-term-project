package net.flowstlc.compiler.ast;

public interface ASTNode {
    <R> R accept(ASTVisitor<R> visitor);

    default SourceSpan getSpan() {
        return SourceSpan.UNKNOWN;
    }
}
