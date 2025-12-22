package net.flowstlc.compiler.ast;

import java.util.Map;

public class RecordType implements Type {
    private final SourceSpan span;
    private final Map<String, Type> fields;

    public RecordType(SourceSpan span, Map<String, Type> fields) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.fields = fields;
    }

    public RecordType(Map<String, Type> fields) {
        this(SourceSpan.UNKNOWN, fields);
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
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitRecordType(this);
    }
}
