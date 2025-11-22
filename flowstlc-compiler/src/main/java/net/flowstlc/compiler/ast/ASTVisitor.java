package net.flowstlc.compiler.ast;

public interface ASTVisitor<R> {
    R visitBinaryExpr(BinaryExpr expr);
    R visitBoolLiteralExpr(BoolLiteralExpr expr);
    R visitBuiltinType(BuiltinType expr);
    R visitConstantDeclaration(ConstantDeclaration declaration);
    R visitFunctionCallExpr(FunctionCallExpr expr);
    R visitFunctionDeclaration(FunctionDeclaration declaration);
    R visitFunctionType(FunctionType type);
    R visitIdentifierExpr(IdentifierExpr expr);
    R visitIfExpr(IfExpr expr);
    R visitIntLiteralExpr(IntLiteralExpr expr);
    R visitLetExpr(LetExpr expr);
    R visitModalityExpr(ModalityExpr type);
    R visitModalityType(ModalityType type);
    R visitProgram(Program program);
    R visitRecordExpr(RecordExpr expr);
    R visitRecordFieldAccessExpr(RecordFieldAccessExpr expr);
    R visitRecordType(RecordType type);
    R visitUnannotatedFunctionType(UnannotatedFunctionType type);
    R visitUnaryExpr(UnaryExpr expr);
    R visitUnitLiteralExpr(UnitLiteralExpr expr);
}
