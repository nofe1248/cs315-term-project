package net.flowstlc.compiler.interpreter;

import java.util.HashMap;
import java.util.Map;

public class Env {
    private final Map<String, Value> map = new HashMap<>();
    private final Env parent;

    public Env() {
        this.parent = null;
    }

    public Env(Env parent) {
        this.parent = parent;
    }

    public void put(String name, Value value) {
        map.put(name, value);
    }

    public Value get(String name) {
        if (map.containsKey(name)) {
            return map.get(name);
        }
        if (parent != null) return parent.get(name);
        throw new RuntimeError("Unbound identifier: " + name);
    }

    public Env extend() {
        return new Env(this);
    }
}
