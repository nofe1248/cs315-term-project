package net.flowstlc.compiler.ast;

import java.util.List;

public class FunctionDeclaration implements Declaration {
    private final String name;
    private final List<String> parameters;
    private final Type type;
    private final Expr body;

    public FunctionDeclaration(String name, List<String> parameters, Type type, Expr body) {
        this.name = name;
        this.parameters = parameters;
        this.type = type;
        this.body = body;
    }

    public String getName() {
        return name;
    }

    public List<String> getParameters() {
        return parameters;
    }

    public Type getType() {
        return type;
    }

    public Expr getBody() {
        return body;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitFunctionDeclaration(this);
    }
}
