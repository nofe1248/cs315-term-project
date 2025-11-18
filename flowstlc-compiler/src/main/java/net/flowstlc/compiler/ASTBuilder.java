package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.*;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

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
        throw new IllegalArgumentException("Unknown declaration: " + ctx.getText());
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
        String name = ctx.function_body_declaration().Identifier().getText();

        // 提取参数列表
        List<String> parameters = new ArrayList<>();
        if (ctx.function_body_declaration().function_argument_list() != null) {
            parameters = ctx.function_body_declaration().function_argument_list().Identifier().stream()
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
    public Object visitLevelSecret(FlowSTLCParser.LevelSecretContext ctx) {
        return SecurityLevel.SECRET;
    }

    @Override
    public Object visitLevelPublic(FlowSTLCParser.LevelPublicContext ctx) {
        return SecurityLevel.PUBLIC;
    }

    // ==================== 类型转换 ====================

    @Override
    public Object visitFunctionType(FlowSTLCParser.FunctionTypeContext ctx) {
        Type from = (Type) visit(ctx.type(0));
        SecurityLevel level = (SecurityLevel) visit(ctx.security_level());
        Type to = (Type) visit(ctx.type(1));
        return new FunctionType(from, level, to);
    }

    @Override
    public Object visitModalityType(FlowSTLCParser.ModalityTypeContext ctx) {
        Type inner = (Type) visit(ctx.type());
        SecurityLevel level = (SecurityLevel) visit(ctx.security_level());
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
    public Object visitLetExpression(FlowSTLCParser.LetExpressionContext ctx) {
        String name = ctx.Identifier().getText();
        Expr bound = (Expr) visit(ctx.simple_expression(0));
        Expr inExpr = (Expr) visit(ctx.simple_expression(1));
        return new LetExpr(name, bound, inExpr);
    }

    @Override
    public Object visitFunctionCall(FlowSTLCParser.FunctionCallContext ctx) {
        String name = ctx.Identifier().getText();
        List<Expr> arguments = new ArrayList<>();
        if (ctx.simple_expression() != null) {
            arguments = ctx.simple_expression().stream()
                    .map(exprCtx -> (Expr) visit(exprCtx))
                    .collect(Collectors.toList());
        }
        return new FunctionCallExpr(name, arguments);
    }

    private BinaryExpr createBinaryExpr(FlowSTLCParser.Simple_expressionContext leftCtx, FlowSTLCParser.Simple_expressionContext rightCtx, BinaryOp op) {
        Expr lhs = (Expr) visit(leftCtx);
        Expr rhs = (Expr) visit(rightCtx);
        return new BinaryExpr(lhs, op, rhs);
    }

    @Override
    public Object visitAddExpression(FlowSTLCParser.AddExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.ADD);
    }

    @Override
    public Object visitSubExpression(FlowSTLCParser.SubExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.SUB);
    }

    @Override
    public Object visitMulExpression(FlowSTLCParser.MulExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.MUL);
    }

    @Override
    public Object visitDivExpression(FlowSTLCParser.DivExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.DIV);
    }

    @Override
    public Object visitModExpression(FlowSTLCParser.ModExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.MOD);
    }

    @Override
    public Object visitAndExpression(FlowSTLCParser.AndExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.AND);
    }

    @Override
    public Object visitOrExpression(FlowSTLCParser.OrExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.OR);
    }

    @Override
    public Object visitEqualExpression(FlowSTLCParser.EqualExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.EQ);
    }

    @Override
    public Object visitNotEqualExpression(FlowSTLCParser.NotEqualExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.NEQ);
    }

    @Override
    public Object visitLessThanExpression(FlowSTLCParser.LessThanExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.LT);
    }

    @Override
    public Object visitLessThanOrEqualExpression(FlowSTLCParser.LessThanOrEqualExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.LTE);
    }

    @Override
    public Object visitGreaterThanExpression(FlowSTLCParser.GreaterThanExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.GT);
    }

    @Override
    public Object visitGreaterThanOrEqualExpression(FlowSTLCParser.GreaterThanOrEqualExpressionContext ctx) {
        return createBinaryExpr(ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.GTE);
    }

    @Override
    public Object visitNotExpression(FlowSTLCParser.NotExpressionContext ctx) {
        Expr expr = (Expr) visit(ctx.simple_expression());
        return new UnaryExpr(UnaryOp.NOT, expr);
    }

    @Override
    public Object visitNegateExpression(FlowSTLCParser.NegateExpressionContext ctx) {
        Expr expr = (Expr) visit(ctx.simple_expression());
        return new UnaryExpr(UnaryOp.NEG, expr);
    }

    @Override
    public Object visitModalityExpression(FlowSTLCParser.ModalityExpressionContext ctx) {
        Expr inner = (Expr) visit(ctx.simple_expression());
        return new ModalityExpr(inner);
    }

    @Override
    public Object visitIfExpression(FlowSTLCParser.IfExpressionContext ctx) {
        Expr condition = (Expr) visit(ctx.simple_expression(0));
        Expr thenBranch = (Expr) visit(ctx.simple_expression(1));
        Expr elseBranch = (Expr) visit(ctx.simple_expression(2));
        return new IfExpr(condition, thenBranch, elseBranch);
    }

    @Override
    public Object visitLiteralExpression(FlowSTLCParser.LiteralExpressionContext ctx) {
        return visit(ctx.literal());
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
