package net.flowstlc.compiler.interpreter;

import net.flowstlc.compiler.ast.*;

import java.util.List;

public final class Interpreter {
    Env global = new Env();
    EvalVisitor eval = new EvalVisitor(global);

    public Value run(Program program) {
        for (Declaration decl : program.getDeclarations()) {
            decl.accept(eval);
        }

        return UnitV.INSTANCE;
    }
    public Value callEntryPoint(String entryPointName) {
        Value v = global.get(entryPointName);
        if (!(v instanceof ClosureV clo)) {
            throw new RuntimeError("Entry point is not a function: " + entryPointName);
        }
        List<String> params = clo.getParams();
        if (params.isEmpty()) {
            // main 无参：直接跑 body
            Env old = evalEnv();
            Env callEnv = clo.getEnv().extend();
            setEvalEnv(callEnv);
            Value res = clo.getBody().accept(eval);
            setEvalEnv(old);
            return res;
        } else if (params.size() == 1) {
            // main(Unit)->T：给一个 unit
            Env old = evalEnv();
            Env callEnv = clo.getEnv().extend();
            callEnv.put(params.get(0), UnitV.INSTANCE);
            setEvalEnv(callEnv);
            Value res = clo.getBody().accept(eval);
            setEvalEnv(old);
            return res;
        } else {
            throw new RuntimeError("Entry point expects " + params.size() + " args, not supported");
        }
    }
    private Env evalEnv() {
        try {
            var f = EvalVisitor.class.getDeclaredField("env");
            f.setAccessible(true);
            return (Env) f.get(eval);
        } catch (Exception e) {
            throw new RuntimeError("Cannot access EvalVisitor env");
        }
    }

    private void setEvalEnv(Env newEnv) {
        try {
            var f = EvalVisitor.class.getDeclaredField("env");
            f.setAccessible(true);
            f.set(eval, newEnv);
        } catch (Exception e) {
            throw new RuntimeError("Cannot set EvalVisitor env");
        }
    }
}
