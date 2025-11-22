package net.flowstlc.compiler.ast;

public class RecordFieldAccessExpr implements Expr {
    private final Expr recordExpr;
    private final String fieldName;

    public RecordFieldAccessExpr(Expr recordExpr, String fieldName) {
        this.recordExpr = recordExpr;
        this.fieldName = fieldName;
    }

    public Expr getRecordExpr() {
        return recordExpr;
    }

    public String getFieldName() {
        return fieldName;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitRecordFieldAccessExpr(this);
    }
}
