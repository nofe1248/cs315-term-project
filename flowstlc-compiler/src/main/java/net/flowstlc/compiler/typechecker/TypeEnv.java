package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.ast.Type;
import net.flowstlc.compiler.ast.SecurityLevel;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public final class TypeEnv {
    private final Map<String, Type> vars;

    public TypeEnv() {
        this.vars = new HashMap<>();
    }

    private TypeEnv(Map<String, Type> vars) {
        this.vars = vars;
    }

    public Type lookupVar(String name) {
        return vars.get(name);
    }

    public TypeEnv extend(String name, Type type) {
        Map<String, Type> copy = new HashMap<>(this.vars);
        copy.put(name, type);
        return new TypeEnv(copy);
    }

    public Map<String, Type> getVars() {
        return Collections.unmodifiableMap(vars);
    }
}
