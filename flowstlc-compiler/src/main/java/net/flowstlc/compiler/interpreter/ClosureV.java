package net.flowstlc.compiler.interpreter;

import net.flowstlc.compiler.ast.Expr;

import java.util.List;

public final class ClosureV implements Value {
    private final List<String> params;
    private final Expr body;
    private final Env env;

    public ClosureV(List<String> params, Expr body, Env env) {
        this.params = params;
        this.body = body;
        this.env = env;
    }

    public List<String> getParams() {
        return params;
    }

    public Expr getBody() {
        return body;
    }

    public Env getEnv() {
        return env;
    }
}
