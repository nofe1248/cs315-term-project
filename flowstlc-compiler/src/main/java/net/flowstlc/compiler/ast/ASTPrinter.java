package net.flowstlc.compiler.ast;

import java.util.List;
import java.util.Objects;
import java.util.Map;

public final class ASTPrinter extends BaseASTVisitor<String> {
    private String indent = "";

    public void print(ASTNode node) {
        String out = Objects.requireNonNullElse(node.accept(this), "");
        System.out.println(out);
    }

    // Helper to print the current node header line
    private String node(String header) {
        return indent + header + System.lineSeparator();
    }

    // Helper to render a single child subtree with a label
    private String child(String label, ASTNode node) {
        StringBuilder sb = new StringBuilder();
        sb.append(indent).append("  ").append(label).append(":").append(System.lineSeparator());
        String prev = indent;
        indent = prev + "    ";
        if (node != null) {
            sb.append(node.accept(this));
        } else {
            sb.append(indent).append("<null>").append(System.lineSeparator());
        }
        indent = prev;
        return sb.toString();
    }

    // Helper to render a labeled simple value on one line
    private String value(String label, String value) {
        return indent + "  " + label + ": " + value + System.lineSeparator();
    }

    // Helper to render a labeled list of child nodes
    private String childList(String label, List<? extends ASTNode> nodes) {
        StringBuilder sb = new StringBuilder();
        sb.append(indent).append("  ").append(label).append(":").append(System.lineSeparator());
        String prev = indent;
        indent = prev + "    ";
        if (nodes == null || nodes.isEmpty()) {
            sb.append(indent).append("<empty>").append(System.lineSeparator());
        } else {
            for (int i = 0; i < nodes.size(); i++) {
                ASTNode n = nodes.get(i);
                sb.append(indent).append("[").append(i).append("]").append(":").append(System.lineSeparator());
                String prev2 = indent;
                indent = prev2 + "    ";
                sb.append(n.accept(this));
                indent = prev2;
            }
        }
        indent = prev;
        return sb.toString();
    }

    @Override
    public String visitProgram(Program program) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("Program"));
        sb.append(childList("declarations", program.getDeclarations()));
        return sb.toString();
    }

    @Override
    public String visitConstantDeclaration(ConstantDeclaration declaration) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("ConstantDeclaration name=" + declaration.getName()));
        sb.append(child("type", declaration.getType()));
        sb.append(child("value", declaration.getValue()));
        return sb.toString();
    }

    @Override
    public String visitFunctionDeclaration(FunctionDeclaration declaration) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("FunctionDeclaration name=" + declaration.getName()));
        String params = declaration.getParameters() == null || declaration.getParameters().isEmpty()
                ? "<none>"
                : String.join(", ", declaration.getParameters());
        sb.append(value("parameters", params));
        sb.append(child("type", declaration.getType()));
        sb.append(child("body", declaration.getBody()));
        return sb.toString();
    }

    // Types
    @Override
    public String visitBuiltinType(BuiltinType expr) {
        return node("BuiltinType kind=" + expr.getKind());
    }

    @Override
    public String visitFunctionType(FunctionType type) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("FunctionType"));
        sb.append(child("from", type.getFrom()));
        sb.append(value("level", String.valueOf(type.getLevel())));
        sb.append(child("to", type.getTo()));
        return sb.toString();
    }

    @Override
    public String visitModalityType(ModalityType type) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("ModalityType"));
        sb.append(child("inner", type.getInner()));
        sb.append(value("level", String.valueOf(type.getLevel())));
        return sb.toString();
    }

    @Override
    public String visitRecordType(RecordType type) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("RecordType"));
        String prev = indent;
        sb.append(indent).append("  ").append("fields:").append(System.lineSeparator());
        indent = prev + "    ";
        Map<String, Type> fields = type.getFields();
        if (fields == null || fields.isEmpty()) {
            sb.append(indent).append("<empty>").append(System.lineSeparator());
        } else {
            for (Map.Entry<String, Type> entry : fields.entrySet()) {
                sb.append(indent).append(entry.getKey()).append(":").append(System.lineSeparator());
                String prev2 = indent;
                indent = prev2 + "    ";
                Type fieldType = entry.getValue();
                if (fieldType != null) {
                    sb.append(fieldType.accept(this));
                } else {
                    sb.append(indent).append("<null>").append(System.lineSeparator());
                }
                indent = prev2;
            }
        }
        indent = prev;
        return sb.toString();
    }

    @Override
    public String visitRecordFieldAccessExpr(RecordFieldAccessExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("RecordFieldAccessExpr field=" + expr.getFieldName()));
        sb.append(child("record", expr.getRecordExpr()));
        return sb.toString();
    }

    @Override
    public String visitRecordExpr(RecordExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("RecordExpr"));
        String prev = indent;
        sb.append(indent).append("  ").append("fields:").append(System.lineSeparator());
        indent = prev + "    ";
        Map<String, Expr> fields = expr.getFields();
        if (fields == null || fields.isEmpty()) {
            sb.append(indent).append("<empty>").append(System.lineSeparator());
        } else {
            for (Map.Entry<String, Expr> entry : fields.entrySet()) {
                sb.append(indent).append(entry.getKey()).append(":").append(System.lineSeparator());
                String prev2 = indent;
                indent = prev2 + "    ";
                Expr fieldExpr = entry.getValue();
                if (fieldExpr != null) {
                    sb.append(fieldExpr.accept(this));
                } else {
                    sb.append(indent).append("<null>").append(System.lineSeparator());
                }
                indent = prev2;
            }
        }
        indent = prev;
        return sb.toString();
    }

    // Expressions
    @Override
    public String visitIdentifierExpr(IdentifierExpr expr) {
        return node("Identifier name=" + expr.getName());
    }

    @Override
    public String visitIntLiteralExpr(IntLiteralExpr expr) {
        return node("IntLiteral value=" + expr.getValue());
    }

    @Override
    public String visitBoolLiteralExpr(BoolLiteralExpr expr) {
        return node("BoolLiteral value=" + expr.getValue());
    }

    @Override
    public String visitUnitLiteralExpr(UnitLiteralExpr expr) {
        return node("UnitLiteral");
    }

    @Override
    public String visitUnaryExpr(UnaryExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("UnaryExpr op=" + expr.getOp()));
        sb.append(child("expr", expr.getExpr()));
        return sb.toString();
    }

    @Override
    public String visitBinaryExpr(BinaryExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("BinaryExpr op=" + expr.getOp()));
        sb.append(child("left", expr.getLeft()));
        sb.append(child("right", expr.getRight()));
        return sb.toString();
    }

    @Override
    public String visitIfExpr(IfExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("IfExpr"));
        sb.append(child("condition", expr.getCondition()));
        sb.append(child("then", expr.getThenBranch()));
        sb.append(child("else", expr.getElseBranch()));
        return sb.toString();
    }

    @Override
    public String visitLetExpr(LetExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("LetExpr name=" + expr.getName()));
        sb.append(child("bound", expr.getBound()));
        sb.append(child("in", expr.getInExpr()));
        return sb.toString();
    }

    @Override
    public String visitFunctionCallExpr(FunctionCallExpr expr) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("FunctionCallExpr name=" + expr.getFunctionName()));
        sb.append(childList("arguments", expr.getArguments()));
        return sb.toString();
    }

    @Override
    public String visitModalityExpr(ModalityExpr type) {
        StringBuilder sb = new StringBuilder();
        sb.append(node("ModalityExpr"));
        sb.append(child("inner", type.getInner()));
        return sb.toString();
    }
}
