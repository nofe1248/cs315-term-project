package net.flowstlc.compiler.ast;

import java.util.Map;

public class RecordType implements Type {
    private final Map<String, Type> fields;

    public RecordType(Map<String, Type> fields) {
        this.fields = fields;
    }

    public Map<String, Type> getFields() {
        return fields;
    }

    public boolean hasField(String fieldName) {
        return fields.containsKey(fieldName);
    }

    public Type getFieldType(String fieldName) {
        return fields.get(fieldName);
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitRecordType(this);
    }
}
