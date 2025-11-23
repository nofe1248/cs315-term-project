package net.flowstlc.compiler.ast;

import java.util.List;

public class IntrinsicExpr implements Expr {
    private final String intrinsicName;
    private final List<Expr> arguments;

    public IntrinsicExpr(String intrinsicName, List<Expr> arguments) {
        this.intrinsicName = intrinsicName;
        this.arguments = arguments;
    }

    public String getIntrinsicName() {
        return intrinsicName;
    }

    public List<Expr> getArguments() {
        return arguments;
    }

    public Expr getArgumentAt(int index) {
        return arguments.get(index);
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitIntrinsicExpr(this);
    }
}
