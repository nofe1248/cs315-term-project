package net.flowstlc.compiler.ast;

import java.util.Map;

public class RecordExpr implements Expr {
    private final Map<String, Expr> fields;

    public RecordExpr(Map<String, Expr> fields) {
        this.fields = fields;
    }

    public Map<String, Expr> getFields() {
        return fields;
    }

    public boolean hasField(String fieldName) {
        return fields.containsKey(fieldName);
    }

    public Expr getFieldExpr(String fieldName) {
        return fields.get(fieldName);
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitRecordExpr(this);
    }
}
