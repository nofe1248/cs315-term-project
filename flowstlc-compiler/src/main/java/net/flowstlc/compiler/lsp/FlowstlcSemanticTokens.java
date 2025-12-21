package net.flowstlc.compiler.lsp;

import net.flowstlc.compiler.FlowSTLCLexer;
import net.flowstlc.compiler.FlowSTLCParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.eclipse.lsp4j.SemanticTokens;
import org.eclipse.lsp4j.SemanticTokensLegend;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class FlowstlcSemanticTokens {
    private FlowstlcSemanticTokens() {
    }

    // Keep these stable: VSCode will cache styling by index.
    public static final List<String> TOKEN_TYPES = List.of(
            "keyword",    // 0
            "type",       // 1
            "number",     // 2
            "string",     // 3
            "boolean",    // 4
            "variable",   // 5
            "function",   // 6
            "property",   // 7
            "operator"    // 8
    );

    public static final List<String> TOKEN_MODIFIERS = List.of(
            "declaration" // bit 0
    );

    public static SemanticTokensLegend legend() {
        return new SemanticTokensLegend(TOKEN_TYPES, TOKEN_MODIFIERS);
    }

    private static final int MOD_DECLARATION = 1 << 0;

    private static final class SemTok {
        final int line; // 0-based
        final int col;  // 0-based
        final int len;
        final int type;
        final int mods;

        private SemTok(int line, int col, int len, int type, int mods) {
            this.line = line;
            this.col = col;
            this.len = len;
            this.type = type;
            this.mods = mods;
        }
    }

    public static SemanticTokens full(String text) {
        if (text == null) {
            return new SemanticTokens(Collections.emptyList());
        }

        FlowSTLCLexer lexer = new FlowSTLCLexer(CharStreams.fromString(text));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        tokens.fill();

        // Parser pass for identifier context.
        FlowSTLCParser parser = new FlowSTLCParser(new CommonTokenStream(new FlowSTLCLexer(CharStreams.fromString(text))));
        ParseTree tree = parser.program();

        Map<Token, SemTok> preferred = new HashMap<>();
        Set<Token> identifierTokens = new HashSet<>();

        collectIdentifierContexts(tree, preferred, identifierTokens);

        List<SemTok> all = new ArrayList<>();

        for (Token t : tokens.getTokens()) {
            if (t == null) continue;
            if (t.getChannel() != Token.DEFAULT_CHANNEL) continue;
            if (t.getType() == Token.EOF) continue;

            int line0 = Math.max(0, t.getLine() - 1);
            int col0 = Math.max(0, t.getCharPositionInLine());
            int len = Math.max(1, t.getStopIndex() - t.getStartIndex() + 1);

            SemTok st = preferred.get(t);
            if (st != null) {
                all.add(st);
                continue;
            }

            int type = classifyLexerTokenType(t.getType());
            if (type < 0) {
                if (t.getType() == FlowSTLCLexer.Identifier) {
                    all.add(new SemTok(line0, col0, len, typeIndex("variable"), 0));
                }
                continue;
            }

            int mods = 0;
            all.add(new SemTok(line0, col0, len, type, mods));
        }

        all.sort(Comparator
                .comparingInt((SemTok s) -> s.line)
                .thenComparingInt(s -> s.col)
                .thenComparingInt(s -> s.len));

        return encode(all);
    }

    private static void collectIdentifierContexts(ParseTree tree,
                                                  Map<Token, SemTok> preferred,
                                                  Set<Token> identifierTokens) {
        walk(tree, n -> {
            if (n instanceof FlowSTLCParser.Function_type_declarationContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "function", MOD_DECLARATION);
            }
            if (n instanceof FlowSTLCParser.Function_body_declarationContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "function", MOD_DECLARATION);
            }
            if (n instanceof FlowSTLCParser.Constant_declarationContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "variable", MOD_DECLARATION);
            }
            if (n instanceof FlowSTLCParser.FunctionCallContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "function", 0);
            }
            if (n instanceof FlowSTLCParser.LetExpressionContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "variable", MOD_DECLARATION);
            }
            if (n instanceof FlowSTLCParser.Record_expr_fieldContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "property", MOD_DECLARATION);
            }
            if (n instanceof FlowSTLCParser.Record_type_fieldContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "property", MOD_DECLARATION);
            }
            if (n instanceof FlowSTLCParser.RecordFieldAccessExpressionContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "property", 0);
            }
            if (n instanceof FlowSTLCParser.IntrinsicExpressionContext ctx) {
                TerminalNode id = ctx.Identifier();
                if (id != null) put(preferred, identifierTokens, id.getSymbol(), "function", 0);
            }
        });
    }

    private static void put(Map<Token, SemTok> preferred, Set<Token> ids, Token tok, String type, int mods) {
        if (tok == null) return;
        ids.add(tok);
        int line0 = Math.max(0, tok.getLine() - 1);
        int col0 = Math.max(0, tok.getCharPositionInLine());
        int len = Math.max(1, tok.getStopIndex() - tok.getStartIndex() + 1);
        preferred.put(tok, new SemTok(line0, col0, len, typeIndex(type), mods));
    }

    private interface NodeConsumer {
        void accept(Object node);
    }

    private static void walk(ParseTree node, NodeConsumer consumer) {
        if (node == null) return;
        consumer.accept(node);
        int n = node.getChildCount();
        for (int i = 0; i < n; i++) {
            var c = node.getChild(i);
            walk(c, consumer);
        }
    }

    private static int typeIndex(String type) {
        int idx = TOKEN_TYPES.indexOf(type);
        if (idx < 0) {
            throw new IllegalArgumentException("Unknown token type: " + type);
        }
        return idx;
    }

    private static int classifyLexerTokenType(int antlrType) {
        if (antlrType == FlowSTLCLexer.KW_FUN
                || antlrType == FlowSTLCLexer.KW_IF
                || antlrType == FlowSTLCLexer.KW_THEN
                || antlrType == FlowSTLCLexer.KW_ELSE
                || antlrType == FlowSTLCLexer.KW_AND
                || antlrType == FlowSTLCLexer.KW_OR
                || antlrType == FlowSTLCLexer.KW_NOT
                || antlrType == FlowSTLCLexer.KW_LET
                || antlrType == FlowSTLCLexer.KW_IN
                || antlrType == FlowSTLCLexer.KW_VAL) {
            return typeIndex("keyword");
        }

        if (antlrType == FlowSTLCLexer.KW_INT
                || antlrType == FlowSTLCLexer.KW_BOOL
                || antlrType == FlowSTLCLexer.KW_STRING
                || antlrType == FlowSTLCLexer.KW_UNIT
                || antlrType == FlowSTLCLexer.KW_SECRET
                || antlrType == FlowSTLCLexer.KW_PUBLIC) {
            return typeIndex("type");
        }

        if (antlrType == FlowSTLCLexer.IntegerLiteral) return typeIndex("number");
        if (antlrType == FlowSTLCLexer.StringLiteral) return typeIndex("string");
        if (antlrType == FlowSTLCLexer.BooleanLiteral) return typeIndex("boolean");
        if (antlrType == FlowSTLCLexer.KW_UNIT_LITERAL) return typeIndex("keyword");

        if (antlrType == FlowSTLCLexer.ASSIGN
                || antlrType == FlowSTLCLexer.EQUAL
                || antlrType == FlowSTLCLexer.NOTEQUAL
                || antlrType == FlowSTLCLexer.LT
                || antlrType == FlowSTLCLexer.GT
                || antlrType == FlowSTLCLexer.LE
                || antlrType == FlowSTLCLexer.GE
                || antlrType == FlowSTLCLexer.ADD
                || antlrType == FlowSTLCLexer.SUB
                || antlrType == FlowSTLCLexer.MUL
                || antlrType == FlowSTLCLexer.DIV
                || antlrType == FlowSTLCLexer.MOD
                || antlrType == FlowSTLCLexer.ARROW
                || antlrType == FlowSTLCLexer.CARET
                || antlrType == FlowSTLCLexer.DOT
                || antlrType == FlowSTLCLexer.AT
                || antlrType == FlowSTLCLexer.COLON) {
            return typeIndex("operator");
        }

        return -1;
    }

    private static SemanticTokens encode(List<SemTok> tokens) {
        List<Integer> data = new ArrayList<>(tokens.size() * 5);

        int prevLine = 0;
        int prevCol = 0;
        boolean first = true;

        for (SemTok t : tokens) {
            if (t.len <= 0) continue;

            int deltaLine;
            int deltaStart;
            if (first) {
                deltaLine = t.line;
                deltaStart = t.col;
                first = false;
            } else {
                deltaLine = t.line - prevLine;
                deltaStart = deltaLine == 0 ? (t.col - prevCol) : t.col;
            }

            data.add(deltaLine);
            data.add(deltaStart);
            data.add(t.len);
            data.add(t.type);
            data.add(t.mods);

            prevLine = t.line;
            prevCol = t.col;
        }

        return new SemanticTokens(data);
    }
}
