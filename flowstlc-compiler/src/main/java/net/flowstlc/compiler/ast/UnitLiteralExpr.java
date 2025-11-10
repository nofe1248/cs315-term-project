package net.flowstlc.compiler.ast;

public final class UnitLiteralExpr implements LiteralExpr {
    public static final UnitLiteralExpr INSTANCE = new UnitLiteralExpr();

    private UnitLiteralExpr() {
    }

    @Override
    public <R> R accept(ASTVisitor<R> visitor) {
        return visitor.visitUnitLiteralExpr(this);
    }
}