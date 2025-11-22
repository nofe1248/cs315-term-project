package net.flowstlc.compiler.interpreter;

import java.util.Map;

public class RecordV implements Value {
    private final Map<String, Value> fields;

    public RecordV(Map<String, Value> fields) {
        this.fields = fields;
    }

    public boolean hasField(String name) {
        return fields.containsKey(name);
    }

    public Value getField(String name) {
        return fields.get(name);
    }

    public Map<String, Value> getFields() {
        return fields;
    }

    @Override
    public String toString() {
        return fields.toString();
    }
}
