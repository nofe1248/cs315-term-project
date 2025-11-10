package net.flowstlc.compiler.ast;

public class BaseASTVisitor<R> implements ASTVisitor<R> {
    protected R defaultResult() {
        return null;
    }

    @Override
    public R visitBinaryExpr(BinaryExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitBoolLiteralExpr(BoolLiteralExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitBuiltinType(BuiltinType expr) {
        return defaultResult();
    }

    @Override
    public R visitConstantDeclaration(ConstantDeclaration declaration) {
        return defaultResult();
    }

    @Override
    public R visitFunctionCallExpr(FunctionCallExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitFunctionDeclaration(FunctionDeclaration declaration) {
        return defaultResult();
    }

    @Override
    public R visitFunctionType(FunctionType type) {
        return defaultResult();
    }

    @Override
    public R visitIdentifierExpr(IdentifierExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitIfExpr(IfExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitIntLiteralExpr(IntLiteralExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitLetExpr(LetExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitModalityExpr(ModalityExpr type) {
        return defaultResult();
    }

    @Override
    public R visitModalityType(ModalityType type) {
        return defaultResult();
    }

    @Override
    public R visitProgram(Program program) {
        return defaultResult();
    }

    @Override
    public R visitUnaryExpr(UnaryExpr expr) {
        return defaultResult();
    }

    @Override
    public R visitUnitLiteralExpr(UnitLiteralExpr expr) {
        return defaultResult();
    }
}
