package net.flowstlc.compiler.ast;

public final class RecordFieldAccessExpr implements Expr {
    private final SourceSpan span;
    private final Expr recordExpr;
    private final String fieldName;

    public RecordFieldAccessExpr(SourceSpan span, Expr recordExpr, String fieldName) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.recordExpr = recordExpr;
        this.fieldName = fieldName;
    }

    public RecordFieldAccessExpr(Expr recordExpr, String fieldName) {
        this(SourceSpan.UNKNOWN, recordExpr, fieldName);
    }

    public Expr getRecordExpr() {
        return recordExpr;
    }

    public String getFieldName() {
        return fieldName;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitRecordFieldAccessExpr(this);
    }
}
