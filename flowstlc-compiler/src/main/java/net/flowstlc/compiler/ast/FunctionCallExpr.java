package net.flowstlc.compiler.ast;

import java.util.List;

public final class FunctionCallExpr implements Expr {
    private final String functionName;
    private final List<Expr> arguments;

    public FunctionCallExpr(String functionName, List<Expr> arguments) {
        this.functionName = functionName;
        this.arguments = arguments;
    }

    public String getFunctionName() {
        return functionName;
    }

    public List<Expr> getArguments() {
        return arguments;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitFunctionCallExpr(this);
    }
}