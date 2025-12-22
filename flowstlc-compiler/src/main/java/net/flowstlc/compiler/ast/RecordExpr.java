package net.flowstlc.compiler.ast;

import java.util.Map;

public final class RecordExpr implements Expr {
    private final SourceSpan span;
    private final Map<String, Expr> fields;

    public RecordExpr(SourceSpan span, Map<String, Expr> fields) {
        this.span = span == null ? SourceSpan.UNKNOWN : span;
        this.fields = fields;
    }

    public RecordExpr(Map<String, Expr> fields) {
        this(SourceSpan.UNKNOWN, fields);
    }

    public Map<String, Expr> getFields() {
        return fields;
    }

    @Override
    public SourceSpan getSpan() {
        return span;
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitRecordExpr(this);
    }
}
