package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.*;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

public final class ASTBuilder extends FlowSTLCParserBaseVisitor<Object> {
    public Program build(FlowSTLCParser.ProgramContext ctx) {
        return (Program) visitProgram(ctx);
    }

    @Override
    public Object visitProgram(FlowSTLCParser.ProgramContext ctx) {
        List<Declaration> declarations = new ArrayList<>();
        for (FlowSTLCParser.DeclarationContext declCtx : ctx.declarations().declaration()) {
            declarations.add((Declaration) visitDeclaration(declCtx));
        }
        return new Program(declarations);
    }

    @Override
    public Object visitDeclarations(FlowSTLCParser.DeclarationsContext ctx) {
        List<Declaration> declarations = new ArrayList<>();
        for (FlowSTLCParser.DeclarationContext declCtx : ctx.declaration()) {
            declarations.add((Declaration) visitDeclaration(declCtx));
        }
        return declarations;
    }

    @Override
    public Object visitDeclaration(FlowSTLCParser.DeclarationContext ctx) {
        if (ctx.constant_declaration() != null) {
            return visitConstant_declaration(ctx.constant_declaration());
        }
        if (ctx.function_declaration() != null) {
            return visitFunction_declaration(ctx.function_declaration());
        }
        throw new IllegalArgumentException("未知声明类型");
    }

    @Override
    public Object visitConstant_declaration(FlowSTLCParser.Constant_declarationContext ctx) {
        String name = ctx.Identifier().getText();
        Type type = (Type) visit(ctx.type());
        Expr value = (Expr) visit(ctx.expr());
        return new ConstantDeclaration(name, type, value);
    }

    @Override
    public Object visitFunction_declaration(FlowSTLCParser.Function_declarationContext ctx) {
        String name = ctx.Identifier().getText();
        
        // 提取参数列表
        List<String> parameters = new ArrayList<>();
        if (ctx.function_argument_list() != null) {
            parameters = ctx.function_argument_list().Identifier().stream()
                    .map(TerminalNode::getText)
                    .collect(Collectors.toList());
        }
        
        Type type = (Type) visit(ctx.function_type_declaration().type());
        Expr body = (Expr) visit(ctx.function_body_declaration().expr());
        
        return new FunctionDeclaration(name, parameters, type, body);
    }

    @Override
    public Object visitFunction_type_declaration(FlowSTLCParser.Function_type_declarationContext ctx) {
        return visit(ctx.type());
    }

    @Override
    public Object visitFunction_body_declaration(FlowSTLCParser.Function_body_declarationContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public Object visitFunction_argument_list(FlowSTLCParser.Function_argument_listContext ctx) {
        return ctx.Identifier().stream()
                .map(TerminalNode::getText)
                .collect(Collectors.toList());
    }

    @Override
    public Object visitLevelSecure(FlowSTLCParser.LevelSecureContext ctx) {
        return SecurityLevel.SECURE;
    }

    @Override
    public Object visitLevelPublic(FlowSTLCParser.LevelPublicContext ctx) {
        return SecurityLevel.PUBLIC;
    }

    // ==================== 类型转换 ====================
    @Override
    public Object visitType(FlowSTLCParser.TypeContext ctx) {
        if (ctx.builtinType() != null) return visitBuiltinType(ctx.builtinType());
        if (ctx.functionType() != null) return visitFunctionType(ctx.functionType());
        if (ctx.modalityType() != null) return visitModalityType(ctx.modalityType());
        throw new IllegalArgumentException("未知类型: " + ctx.getText());
    }

    @Override
    public Object visitBuiltinType(FlowSTLCParser.BuiltinTypeContext ctx) {
        if (ctx.intType() != null) return visitIntType(ctx.intType());
        if (ctx.boolType() != null) return visitBoolType(ctx.boolType());
        if (ctx.unitType() != null) return visitUnitType(ctx.unitType());
        throw new IllegalArgumentException("未知内置类型");
    }

    @Override
    public Object visitFunctionType(FlowSTLCParser.FunctionTypeContext ctx) {
        Type from = (Type) visit(ctx.type(0));
        SecurityLevel level = (SecurityLevel) visit(ctx.securityLevel());
        Type to = (Type) visit(ctx.type(1));
        return new FunctionType(from, level, to);
    }

    @Override
    public Object visitModalityType(FlowSTLCParser.ModalityTypeContext ctx) {
        Type inner = (Type) visit(ctx.type());
        SecurityLevel level = (SecurityLevel) visit(ctx.securityLevel());
        return new ModalityType(inner, level);
    }

    @Override
    public Object visitIntType(FlowSTLCParser.IntTypeContext ctx) {
        return new BuiltinType(BuiltinKind.INT);
    }

    @Override
    public Object visitUnitType(FlowSTLCParser.UnitTypeContext ctx) {
        return new BuiltinType(BuiltinKind.UNIT);
    }

    @Override
    public Object visitBoolType(FlowSTLCParser.BoolTypeContext ctx) {
        return new BuiltinType(BuiltinKind.BOOL);
    }

    // ==================== 表达式转换 ====================
    @Override
    public Object visitExpr(FlowSTLCParser.ExprContext ctx) {
        if (ctx.letExpression() != null) return visitLetExpression(ctx.letExpression());
        if (ctx.ifExpression() != null) return visitIfExpression(ctx.ifExpression());
        if (ctx.orExpression() != null) return visitOrExpression(ctx.orExpression());
        if (ctx.andExpression() != null) return visitAndExpression(ctx.andExpression());
        if (ctx.addExpression() != null) return visitAddExpression(ctx.addExpression());
        if (ctx.subExpression() != null) return visitSubExpression(ctx.subExpression());
        if (ctx.mulExpression() != null) return visitMulExpression(ctx.mulExpression());
        if (ctx.divExpression() != null) return visitDivExpression(ctx.divExpression());
        if (ctx.modExpression() != null) return visitModExpression(ctx.modExpression());
        if (ctx.notExpression() != null) return visitNotExpression(ctx.notExpression());
        if (ctx.negateExpression() != null) return visitNegateExpression(ctx.negateExpression());
        if (ctx.modalityExpression() != null) return visitModalityExpression(ctx.modalityExpression());
        if (ctx.simpleExpression() != null) return visitSimpleExpression(ctx.simpleExpression());
        throw new IllegalArgumentException("未知表达式: " + ctx.getText());
    }

    @Override
    public Object visitSimpleExpression(FlowSTLCParser.SimpleExpressionContext ctx) {
        if (ctx.literalExpression() != null) return visitLiteralExpression(ctx.literalExpression());
        if (ctx.identifierExpression() != null) return visitIdentifierExpression(ctx.identifierExpression());
        if (ctx.functionCall() != null) return visitFunctionCall(ctx.functionCall());
        if (ctx.parenthesizedExpression() != null) return visitParenthesizedExpression(ctx.parenthesizedExpression());
        throw new IllegalArgumentException("未知简单表达式");
    }

    @Override
    public Object visitLetExpression(FlowSTLCParser.LetExpressionContext ctx) {
        String name = ctx.Identifier().getText();
        Expr bound = (Expr) visit(ctx.expr(0));
        Expr inExpr = (Expr) visit(ctx.expr(1));
        return new LetExpr(name, bound, inExpr);
    }

    @Override
    public Object visitFunctionCall(FlowSTLCParser.FunctionCallContext ctx) {
        String name = ctx.Identifier().getText();
        List<Expr> arguments = new ArrayList<>();
        if (ctx.exprList() != null) {
            arguments = ctx.exprList().expr().stream()
                    .map(exprCtx -> (Expr) visit(exprCtx))
                    .collect(Collectors.toList());
        }
        return new FunctionCallExpr(name, arguments);
    }

    @Override
    public Object visitAddExpression(FlowSTLCParser.AddExpressionContext ctx) {
        return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.ADD);
    }

    @Override
    public Object visitSubExpression(FlowSTLCParser.SubExpressionContext ctx) {
        return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.SUB);
    }

    @Override
    public Object visitMulExpression(FlowSTLCParser.MulExpressionContext ctx) {
        return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.MUL);
    }

    @Override
    public Object visitDivExpression(FlowSTLCParser.DivExpressionContext ctx) {
        return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.DIV);
    }

    @Override
    public Object visitModExpression(FlowSTLCParser.ModExpressionContext ctx) {
        return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.MOD);
    }

    @Override
    public Object visitAndExpression(FlowSTLCParser.AndExpressionContext ctx) {
         return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.AND);
    }

    @Override
    public Object visitOrExpression(FlowSTLCParser.OrExpressionContext ctx) {
        return createBinaryExpr(ctx.expr(0), ctx.expr(1), BinaryOp.OR);
    }

    @Override
    public Object visitNotExpression(FlowSTLCParser.NotExpressionContext ctx) {
        Expr expr = (Expr) visit(ctx.expr());
        return new UnaryExpr(UnaryOp.NOT, expr);
    }

    @Override
    public Object visitNegateExpression(FlowSTLCParser.NegateExpressionContext ctx) {
        Expr expr = (Expr) visit(ctx.expr());
        return new UnaryExpr(UnaryOp.NEG, expr);
    }

    @Override
    public Object visitModalityExpression(FlowSTLCParser.ModalityExpressionContext ctx) {
        Expr inner = (Expr) visit(ctx.expr());
        return new ModalityExpr(inner);
    }

    @Override
    public Object visitIfExpression(FlowSTLCParser.IfExpressionContext ctx) {
        Expr condition = (Expr) visit(ctx.expr(0));
        Expr thenBranch = (Expr) visit(ctx.expr(1));
        Expr elseBranch = (Expr) visit(ctx.expr(2));
        return new IfExpr(condition, thenBranch, elseBranch);
    }

    @Override
    public Object visitLiteralExpression(FlowSTLCParser.LiteralExpressionContext ctx) {
        if (ctx.intLiteral() != null) return visitIntLiteral(ctx.intLiteral());
        if (ctx.boolLiteral() != null) return visitBoolLiteral(ctx.boolLiteral());
        if (ctx.unitLiteral() != null) return visitUnitLiteral(ctx.unitLiteral());
        throw new IllegalArgumentException("未知字面量: " + ctx.getText());
    }

    @Override
    public Object visitParenthesizedExpression(FlowSTLCParser.ParenthesizedExpressionContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public Object visitIdentifierExpression(FlowSTLCParser.IdentifierExpressionContext ctx) {
        return new IdentifierExpr(ctx.Identifier().getText());
    }

    @Override
    public Object visitIntLiteral(FlowSTLCParser.IntLiteralContext ctx) {
        BigInteger value = new BigInteger(ctx.IntegerLiteral().getText());
        return new IntLiteralExpr(value);
    }

    @Override
    public Object visitBoolLiteral(FlowSTLCParser.BoolLiteralContext ctx) {
        boolean value = Boolean.parseBoolean(ctx.BooleanLiteral().getText());
        return new BoolLiteralExpr(value);
    }

    @Override
    public Object visitUnitLiteral(FlowSTLCParser.UnitLiteralContext ctx) {
        return UnitLiteralExpr.INSTANCE;
    }
}
