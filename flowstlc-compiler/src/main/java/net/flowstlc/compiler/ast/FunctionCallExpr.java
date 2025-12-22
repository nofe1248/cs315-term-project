package net.flowstlc.compiler.ast;

import java.util.List;

public final class FunctionCallExpr implements Expr {
    private final SourceSpan span;
    private final String functionName;
    private final List<Expr> arguments;

    public FunctionCallExpr(SourceSpan span, String functionName, List<Expr> arguments) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.functionName = functionName;
        this.arguments = arguments;
    }

    public FunctionCallExpr(String functionName, List<Expr> arguments) {
        this(SourceSpan.UNKNOWN, functionName, arguments);
    }

    public String getFunctionName() {
        return functionName;
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
        return visitor.visitFunctionCallExpr(this);
    }
}