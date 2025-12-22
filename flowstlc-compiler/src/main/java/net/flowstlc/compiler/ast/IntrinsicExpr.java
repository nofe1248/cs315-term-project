package net.flowstlc.compiler.ast;

import java.util.List;

public final class IntrinsicExpr implements Expr {
    private final SourceSpan span;
    private final String intrinsicName;
    private final List<Expr> arguments;

    public IntrinsicExpr(SourceSpan span, String intrinsicName, List<Expr> arguments) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.intrinsicName = intrinsicName;
        this.arguments = arguments;
    }

    public IntrinsicExpr(String intrinsicName, List<Expr> arguments) {
        this(SourceSpan.UNKNOWN, intrinsicName, arguments);
    }

    public String getIntrinsicName() {
        return intrinsicName;
    }

    public List<Expr> getArguments() {
        return arguments;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIntrinsicExpr(this);
    }
}
