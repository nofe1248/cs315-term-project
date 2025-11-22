package net.flowstlc.compiler.ast;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

// Traverses an AST and removes all security labels from types
public class ASTUnannotator extends BaseASTVisitor<ASTNode> {

    public Program unannotate(Program program) {
        return (Program) visitProgram(program);
    }

    /* ================= Program / Declarations ================= */

    @Override
    public ASTNode visitProgram(Program program) {
        List<Declaration> newDecls = new ArrayList<>();
        for (Declaration d : program.getDeclarations()) {
            newDecls.add((Declaration) d.accept(this));
        }
        return new Program(newDecls);
    }

    @Override
    public ASTNode visitFunctionDeclaration(FunctionDeclaration declaration) {
        String name = declaration.getName();
        List<String> params = declaration.getParameters();

        Type newType = (Type) declaration.getType().accept(this);
        Expr newBody = (Expr) declaration.getBody().accept(this);

        return new FunctionDeclaration(name, params, newType, newBody);
    }

    @Override
    public ASTNode visitConstantDeclaration(ConstantDeclaration declaration) {
        String name = declaration.getName();
        Type newType = (Type) declaration.getType().accept(this);
        Expr newValue = (Expr) declaration.getValue().accept(this);

        return new ConstantDeclaration(name, newType, newValue);
    }

    /* ================= Types ================= */

    @Override
    public ASTNode visitBuiltinType(BuiltinType type) {
        return type;
    }

    @Override
    public ASTNode visitModalityType(ModalityType type) {
        return type.getInner().accept(this);
    }

    @Override
    public ASTNode visitFunctionType(FunctionType type) {
        Type newFrom = (Type) type.getFrom().accept(this);
        Type newTo   = (Type) type.getTo().accept(this);

        return new UnannotatedFunctionType(newFrom, newTo);
    }

    @Override
    public ASTNode visitUnannotatedFunctionType(UnannotatedFunctionType type) {
        Type newFrom = (Type) type.getFrom().accept(this);
        Type newTo   = (Type) type.getTo().accept(this);
        return new UnannotatedFunctionType(newFrom, newTo);
    }

    /* ================= Expressions ================= */

    @Override
    public ASTNode visitIdentifierExpr(IdentifierExpr expr) {
        return expr;
    }

    @Override
    public ASTNode visitIntLiteralExpr(IntLiteralExpr expr) {
        return expr;
    }

    @Override
    public ASTNode visitBoolLiteralExpr(BoolLiteralExpr expr) {
        return expr;
    }

    @Override
    public ASTNode visitUnitLiteralExpr(UnitLiteralExpr expr) {
        return expr;
    }

    @Override
    public ASTNode visitLetExpr(LetExpr expr) {
        Expr newBound = (Expr) expr.getBound().accept(this);
        Expr newIn    = (Expr) expr.getInExpr().accept(this);
        return new LetExpr(expr.getName(), newBound, newIn);
    }

    @Override
    public ASTNode visitIfExpr(IfExpr expr) {
        Expr newCond = (Expr) expr.getCondition().accept(this);
        Expr newThen = (Expr) expr.getThenBranch().accept(this);
        Expr newElse = (Expr) expr.getElseBranch().accept(this);
        return new IfExpr(newCond, newThen, newElse);
    }

    @Override
    public ASTNode visitBinaryExpr(BinaryExpr expr) {
        Expr newLeft  = (Expr) expr.getLeft().accept(this);
        Expr newRight = (Expr) expr.getRight().accept(this);
        return new BinaryExpr(newLeft, expr.getOp(), newRight);
    }

    @Override
    public ASTNode visitUnaryExpr(UnaryExpr expr) {
        Expr newInner = (Expr) expr.getExpr().accept(this);
        return new UnaryExpr(expr.getOp(), newInner);
    }

    @Override
    public ASTNode visitFunctionCallExpr(FunctionCallExpr expr) {
        List<Expr> newArgs = new ArrayList<>();
        for (Expr a : expr.getArguments()) {
            newArgs.add((Expr) a.accept(this));
        }
        return new FunctionCallExpr(expr.getFunctionName(), newArgs);
    }
    @Override
    public ASTNode visitRecordExpr(RecordExpr expr) {
        // RecordExpr 里没有安全标签，本质是递归去子表达式即可
        Map<String, Expr> newFields = new LinkedHashMap<>();
        for (Map.Entry<String, Expr> e : expr.getFields().entrySet()) {
            Expr v = (Expr) e.getValue().accept(this);
            newFields.put(e.getKey(), v);
        }
        return new RecordExpr(newFields);
    }

    @Override
    public ASTNode visitRecordFieldAccessExpr(RecordFieldAccessExpr expr) {
        Expr newRec = (Expr) expr.getRecordExpr().accept(this);
        return new RecordFieldAccessExpr(newRec, expr.getFieldName());
    }

    @Override
    public ASTNode visitRecordType(RecordType type) {
        Map<String, Type> newFields = new LinkedHashMap<>();
        for (Map.Entry<String, Type> e : type.getFields().entrySet()) {
            Type t = (Type) e.getValue().accept(this);
            newFields.put(e.getKey(), t);
        }
        return new RecordType(newFields);
    }


    @Override
    public ASTNode visitModalityExpr(ModalityExpr expr) {
        return expr.getInner().accept(this);
    }
}
