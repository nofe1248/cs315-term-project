package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.ast.Type;
import net.flowstlc.compiler.ast.SecurityLevel;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public final class TypeEnv {
    public static final class VarBinding {
        public final Type type;
        public final SecurityLevel grade;

        public VarBinding(Type type, SecurityLevel grade) {
            this.type = type;
            this.grade = grade;
        }
    }

    private final Map<String, VarBinding> vars;

    public TypeEnv() {
        this.vars = new HashMap<>();
    }

    private TypeEnv(Map<String, VarBinding> vars) {
        this.vars = vars;
    }

    public VarBinding lookupVar(String name) {
        return vars.get(name);
    }

    public TypeEnv extend(String name, Type type, SecurityLevel grade) {
        Map<String, VarBinding> copy = new HashMap<>(this.vars);
        copy.put(name, new VarBinding(type, grade));
        return new TypeEnv(copy);
    }

    public Map<String, VarBinding> getVars() {
        return Collections.unmodifiableMap(vars);
    }
}

