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
        return super.visitDeclarations(ctx);
    }

    @Override
    public Object visitDeclaration(FlowSTLCParser.DeclarationContext ctx) {
        return super.visitDeclaration(ctx);
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
        return super.visitFunction_declaration(ctx);
    }

    @Override
    public Object visitFunction_type_declaration(FlowSTLCParser.Function_type_declarationContext ctx) {
        return super.visitFunction_type_declaration(ctx);
    }

    @Override
    public Object visitFunction_body_declaration(FlowSTLCParser.Function_body_declarationContext ctx) {
        return super.visitFunction_body_declaration(ctx);
    }

    @Override
    public Object visitFunction_argument_list(FlowSTLCParser.Function_argument_listContext ctx) {
        return super.visitFunction_argument_list(ctx);
    }

    @Override
    public Object visitLevelSecure(FlowSTLCParser.LevelSecureContext ctx) {
        return super.visitLevelSecure(ctx);
    }

    @Override
    public Object visitLevelPublic(FlowSTLCParser.LevelPublicContext ctx) {
        return super.visitLevelPublic(ctx);
    }

    @Override
    public Object visitBuiltinType(FlowSTLCParser.BuiltinTypeContext ctx) {
        return super.visitBuiltinType(ctx);
    }

    @Override
    public Object visitFunctionType(FlowSTLCParser.FunctionTypeContext ctx) {
        return super.visitFunctionType(ctx);
    }

    @Override
    public Object visitModalityType(FlowSTLCParser.ModalityTypeContext ctx) {
        return super.visitModalityType(ctx);
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

    @Override
    public Object visitSimpleExpression(FlowSTLCParser.SimpleExpressionContext ctx) {
        return super.visitSimpleExpression(ctx);
    }

    @Override
    public Object visitLetExpression(FlowSTLCParser.LetExpressionContext ctx) {
        return super.visitLetExpression(ctx);
    }

    @Override
    public Object visitFunctionCall(FlowSTLCParser.FunctionCallContext ctx) {
        return super.visitFunctionCall(ctx);
    }

    @Override
    public Object visitAddExpression(FlowSTLCParser.AddExpressionContext ctx) {
        return super.visitAddExpression(ctx);
    }

    @Override
    public Object visitSubExpression(FlowSTLCParser.SubExpressionContext ctx) {
        return super.visitSubExpression(ctx);
    }

    @Override
    public Object visitMulExpression(FlowSTLCParser.MulExpressionContext ctx) {
        return super.visitMulExpression(ctx);
    }

    @Override
    public Object visitDivExpression(FlowSTLCParser.DivExpressionContext ctx) {
        return super.visitDivExpression(ctx);
    }

    @Override
    public Object visitModExpression(FlowSTLCParser.ModExpressionContext ctx) {
        return super.visitModExpression(ctx);
    }

    @Override
    public Object visitAndExpression(FlowSTLCParser.AndExpressionContext ctx) {
        return super.visitAndExpression(ctx);
    }

    @Override
    public Object visitOrExpression(FlowSTLCParser.OrExpressionContext ctx) {
        return super.visitOrExpression(ctx);
    }

    @Override
    public Object visitNotExpression(FlowSTLCParser.NotExpressionContext ctx) {
        return super.visitNotExpression(ctx);
    }

    @Override
    public Object visitNegateExpression(FlowSTLCParser.NegateExpressionContext ctx) {
        return super.visitNegateExpression(ctx);
    }

    @Override
    public Object visitModalityExpression(FlowSTLCParser.ModalityExpressionContext ctx) {
        return super.visitModalityExpression(ctx);
    }

    @Override
    public Object visitIfExpression(FlowSTLCParser.IfExpressionContext ctx) {
        return super.visitIfExpression(ctx);
    }

    @Override
    public Object visitLiteralExpression(FlowSTLCParser.LiteralExpressionContext ctx) {
        return super.visitLiteralExpression(ctx);
    }

    @Override
    public Object visitParenthesizedExpression(FlowSTLCParser.ParenthesizedExpressionContext ctx) {
        return super.visitParenthesizedExpression(ctx);
    }

    @Override
    public Object visitIdentifierExpression(FlowSTLCParser.IdentifierExpressionContext ctx) {
        return super.visitIdentifierExpression(ctx);
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
