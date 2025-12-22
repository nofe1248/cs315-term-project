package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public final class ASTBuilder extends FlowSTLCParserBaseVisitor<Object> {
    public Program build(FlowSTLCParser.ProgramContext ctx) {
        return (Program) visitProgram(ctx);
    }

    private static SourceSpan span(ParserRuleContext ctx) {
        if (ctx == null) {
            return SourceSpan.UNKNOWN;
        }
        Token start = ctx.getStart();
        Token stop = ctx.getStop();
        if (start == null || stop == null) {
            return SourceSpan.UNKNOWN;
        }
        int startIdx = start.getStartIndex();
        int stopIdx = stop.getStopIndex();
        if (startIdx < 0 || stopIdx < startIdx) {
            return SourceSpan.UNKNOWN;
        }
        return new SourceSpan(startIdx, stopIdx + 1);
    }

    private static SourceSpan span(TerminalNode node) {
        if (node == null || node.getSymbol() == null) {
            return SourceSpan.UNKNOWN;
        }
        Token t = node.getSymbol();
        int startIdx = t.getStartIndex();
        int stopIdx = t.getStopIndex();
        if (startIdx < 0 || stopIdx < startIdx) {
            return SourceSpan.UNKNOWN;
        }
        return new SourceSpan(startIdx, stopIdx + 1);
    }

    @Override
    public Object visitProgram(FlowSTLCParser.ProgramContext ctx) {
        List<Declaration> declarations = new ArrayList<>();
        for (FlowSTLCParser.DeclarationContext declCtx : ctx.declarations().declaration()) {
            declarations.add((Declaration) visitDeclaration(declCtx));
        }
        return new Program(span(ctx), declarations);
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
        return new ConstantDeclaration(span(ctx), name, type, value);
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

        return new FunctionDeclaration(span(ctx), name, parameters, type, body);
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
    public Object visitFunction_type(FlowSTLCParser.Function_typeContext ctx) {
        Type from = (Type) visit(ctx.modality_type());
        if (ctx.security_level() == null) {
            return from;
        }
        SecurityLevel level = (SecurityLevel) visit(ctx.security_level());
        Type to = (Type) visit(ctx.function_type());
        return new FunctionType(span(ctx), from, level, to);
    }

    @Override
    public Object visitModality_type(FlowSTLCParser.Modality_typeContext ctx) {
        if (ctx.LBRACE() != null) {
            Map<String, Type> fields = ctx.record_type_field().stream()
                    .collect(Collectors.toMap(
                            fieldCtx -> fieldCtx.Identifier().getText(),
                            fieldCtx -> (Type) visit(fieldCtx.type()),
                            (a, b) -> {
                                throw new IllegalArgumentException("Duplicate record field");
                            },
                            LinkedHashMap::new
                    ));
            return new RecordType(span(ctx), fields);
        }
        if (ctx.base_type() != null) {
            return visit(ctx.base_type());
        }
        Type inner = (Type) visit(ctx.modality_type());
        SecurityLevel level = (SecurityLevel) visit(ctx.security_level());
        return new ModalityType(span(ctx), inner, level);
    }

    @Override
    public Object visitBase_type(FlowSTLCParser.Base_typeContext ctx) {
        if (ctx.builtin_type() != null) {
            return visit(ctx.builtin_type());
        }
        return visit(ctx.type());
    }

    @Override
    public Object visitIntType(FlowSTLCParser.IntTypeContext ctx) {
        return new BuiltinType(span(ctx), BuiltinKind.INT);
    }

    @Override
    public Object visitUnitType(FlowSTLCParser.UnitTypeContext ctx) {
        return new BuiltinType(span(ctx), BuiltinKind.UNIT);
    }

    @Override
    public Object visitBoolType(FlowSTLCParser.BoolTypeContext ctx) {
        return new BuiltinType(span(ctx), BuiltinKind.BOOL);
    }

    @Override
    public Object visitStringType(FlowSTLCParser.StringTypeContext ctx) {
        return new BuiltinType(span(ctx), BuiltinKind.STRING);
    }

    // ==================== 表达式转换 ====================

    @Override
    public Object visitSequenceExpression(FlowSTLCParser.SequenceExpressionContext ctx) {
        Expr first = (Expr) visit(ctx.expr(0));
        Expr second = (Expr) visit(ctx.expr(1));
        return new SequenceExpr(span(ctx), first, second);
    }

    @Override
    public Object visitLetExpression(FlowSTLCParser.LetExpressionContext ctx) {
        String name = ctx.Identifier().getText();
        Expr bound = (Expr) visit(ctx.simple_expression(0));
        Expr inExpr = (Expr) visit(ctx.simple_expression(1));
        return new LetExpr(span(ctx), name, bound, inExpr);
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
        return new FunctionCallExpr(span(ctx), name, arguments);
    }

    private BinaryExpr createBinaryExpr(ParserRuleContext wholeCtx,
                                        FlowSTLCParser.Simple_expressionContext leftCtx,
                                        FlowSTLCParser.Simple_expressionContext rightCtx,
                                        BinaryOp op) {
        Expr lhs = (Expr) visit(leftCtx);
        Expr rhs = (Expr) visit(rightCtx);
        return new BinaryExpr(span(wholeCtx), lhs, op, rhs);
    }

    @Override
    public Object visitIntrinsicExpression(FlowSTLCParser.IntrinsicExpressionContext ctx) {
        String name = ctx.Identifier().getText();
        List<Expr> arguments = new ArrayList<>();
        if (ctx.simple_expression() != null) {
            arguments = ctx.simple_expression().stream()
                    .map(exprCtx -> (Expr) visit(exprCtx))
                    .collect(Collectors.toList());
        }
        return new IntrinsicExpr(span(ctx), name, arguments);
    }

    @Override
    public Object visitAddExpression(FlowSTLCParser.AddExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.ADD);
    }

    @Override
    public Object visitSubExpression(FlowSTLCParser.SubExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.SUB);
    }

    @Override
    public Object visitMulExpression(FlowSTLCParser.MulExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.MUL);
    }

    @Override
    public Object visitDivExpression(FlowSTLCParser.DivExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.DIV);
    }

    @Override
    public Object visitModExpression(FlowSTLCParser.ModExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.MOD);
    }

    @Override
    public Object visitAndExpression(FlowSTLCParser.AndExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.AND);
    }

    @Override
    public Object visitOrExpression(FlowSTLCParser.OrExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.OR);
    }

    @Override
    public Object visitEqualExpression(FlowSTLCParser.EqualExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.EQ);
    }

    @Override
    public Object visitNotEqualExpression(FlowSTLCParser.NotEqualExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.NEQ);
    }

    @Override
    public Object visitLessThanExpression(FlowSTLCParser.LessThanExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.LT);
    }

    @Override
    public Object visitLessThanOrEqualExpression(FlowSTLCParser.LessThanOrEqualExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.LTE);
    }

    @Override
    public Object visitGreaterThanExpression(FlowSTLCParser.GreaterThanExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.GT);
    }

    @Override
    public Object visitGreaterThanOrEqualExpression(FlowSTLCParser.GreaterThanOrEqualExpressionContext ctx) {
        return createBinaryExpr(ctx, ctx.simple_expression(0), ctx.simple_expression(1), BinaryOp.GTE);
    }

    @Override
    public Object visitNotExpression(FlowSTLCParser.NotExpressionContext ctx) {
        Expr expr = (Expr) visit(ctx.simple_expression());
        return new UnaryExpr(span(ctx), UnaryOp.NOT, expr);
    }

    @Override
    public Object visitNegateExpression(FlowSTLCParser.NegateExpressionContext ctx) {
        Expr expr = (Expr) visit(ctx.simple_expression());
        return new UnaryExpr(span(ctx), UnaryOp.NEG, expr);
    }

    @Override
    public Object visitModalityExpression(FlowSTLCParser.ModalityExpressionContext ctx) {
        Expr inner = (Expr) visit(ctx.simple_expression());
        return new ModalityExpr(span(ctx), inner);
    }

    @Override
    public Object visitIfExpression(FlowSTLCParser.IfExpressionContext ctx) {
        Expr condition = (Expr) visit(ctx.simple_expression(0));
        Expr thenBranch = (Expr) visit(ctx.simple_expression(1));
        Expr elseBranch = (Expr) visit(ctx.simple_expression(2));
        return new IfExpr(span(ctx), condition, thenBranch, elseBranch);
    }

    @Override
    public Object visitRecordExpression(FlowSTLCParser.RecordExpressionContext ctx) {
        Map<String, Expr> fields = ctx.record_expr_field().stream()
                .collect(Collectors.toMap(
                        fieldCtx -> fieldCtx.Identifier().getText(),
                        fieldCtx -> (Expr) visit(fieldCtx.simple_expression()),
                        (a, b) -> {
                            throw new IllegalArgumentException("Duplicate record field");
                        },
                        LinkedHashMap::new
                ));
        return new RecordExpr(span(ctx), fields);
    }

    @Override
    public Object visitRecordFieldAccessExpression(FlowSTLCParser.RecordFieldAccessExpressionContext ctx) {
        Expr recordExpr = (Expr) visit(ctx.simple_expression());
        String fieldName = ctx.Identifier().getText();
        return new RecordFieldAccessExpr(span(ctx), recordExpr, fieldName);
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
        return new IdentifierExpr(span(ctx.Identifier()), ctx.Identifier().getText());
    }

    @Override
    public Object visitIntLiteral(FlowSTLCParser.IntLiteralContext ctx) {
        BigInteger value = new BigInteger(ctx.IntegerLiteral().getText());
        return new IntLiteralExpr(span(ctx.IntegerLiteral()), value);
    }

    @Override
    public Object visitBoolLiteral(FlowSTLCParser.BoolLiteralContext ctx) {
        boolean value = Boolean.parseBoolean(ctx.BooleanLiteral().getText());
        return new BoolLiteralExpr(span(ctx.BooleanLiteral()), value);
    }

    @Override
    public Object visitUnitLiteral(FlowSTLCParser.UnitLiteralContext ctx) {
        return new UnitLiteralExpr(span(ctx));
    }

    @Override
    public Object visitStringLiteral(FlowSTLCParser.StringLiteralContext ctx) {
        String text = ctx.StringLiteral().getText();
        String raw = text.substring(1, text.length() - 1);
        String value = unescapeString(raw);
        return new StringLiteralExpr(span(ctx.StringLiteral()), value);
    }

    private String unescapeString(String s) {
        StringBuilder sb = new StringBuilder(s.length());
        for (int i = 0; i < s.length(); ) {
            char c = s.charAt(i);
            if (c != '\\') {
                sb.append(c);
                i++;
                continue;
            }
            if (i + 1 >= s.length()) {
                throw new IllegalArgumentException("Invalid escape sequence at end of string");
            }
            char esc = s.charAt(i + 1);
            switch (esc) {
                case 'b':
                    sb.append('\b');
                    i += 2;
                    break;
                case 't':
                    sb.append('\t');
                    i += 2;
                    break;
                case 'n':
                    sb.append('\n');
                    i += 2;
                    break;
                case 'f':
                    sb.append('\f');
                    i += 2;
                    break;
                case 'r':
                    sb.append('\r');
                    i += 2;
                    break;
                case '"':
                    sb.append('"');
                    i += 2;
                    break;
                case '\'':
                    sb.append('\'');
                    i += 2;
                    break;
                case '\\':
                    sb.append('\\');
                    i += 2;
                    break;
                case 'u':
                    if (i + 2 >= s.length() || s.charAt(i + 2) != '{') {
                        throw new IllegalArgumentException("Invalid unicode escape sequence at index " + i + ": missing '{'");
                    }
                    int braceClose = s.indexOf('}', i + 3);
                    if (braceClose == -1) {
                        throw new IllegalArgumentException("Invalid unicode escape sequence at index " + i + ": missing '}'");
                    }
                    String hex = s.substring(i + 3, braceClose);
                    if (hex.isEmpty() || hex.length() > 6 || !hex.matches("[0-9a-fA-F]+")) {
                        throw new IllegalArgumentException("Invalid unicode escape value: " + hex);
                    }
                    int codepoint;
                    try {
                        codepoint = Integer.parseInt(hex, 16);
                    } catch (NumberFormatException e) {
                        throw new IllegalArgumentException("Invalid unicode escape value: " + hex, e);
                    }
                    sb.append(Character.toChars(codepoint));
                    i = braceClose + 1;
                    break;
                default:
                    throw new IllegalArgumentException("Unsupported escape sequence: \\" + esc);
            }
        }
        return sb.toString();
    }
}
