package net.flowstlc.compiler.lsp;

import net.flowstlc.compiler.ast.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public final class TypePrettyPrinter {
    private TypePrettyPrinter() {}

    public static String pretty(Type ty) {
        return pretty(ty, 0);
    }

    private static String pretty(Type ty, int parentPrecedence) {
        if (ty == null) return "<unknown>";

        if (ty instanceof FunctionType ft) {
            String s = pretty(ft.getFrom(), 1)
                    + " ^" + prettyLevel(ft.getLevel())
                    + " -> " + pretty(ft.getTo(), 0);
            return maybeParen(s, parentPrecedence > 0);
        }
        if (ty instanceof UnannotatedFunctionType uft) {
            String s = pretty(uft.getFrom(), 1) + " -> " + pretty(uft.getTo(), 0);
            return maybeParen(s, parentPrecedence > 0);
        }

        if (ty instanceof ModalityType mt) {
            String inner = pretty(mt.getInner(), 2);
            return inner + " [" + prettyLevel(mt.getLevel()) + "]";
        }

        if (ty instanceof BuiltinType bt) {
            return prettyBuiltin(bt.getKind());
        }
        if (ty instanceof RecordType rt) {
            return prettyRecord(rt.getFields());
        }

        return ty.getClass().getSimpleName();
    }

    private static String maybeParen(String s, boolean paren) {
        return paren ? "(" + s + ")" : s;
    }

    private static String prettyBuiltin(BuiltinKind kind) {
        if (kind == null) return "<builtin>";
        return switch (kind) {
            case INT -> "Int";
            case BOOL -> "Bool";
            case STRING -> "String";
            case UNIT -> "Unit";
        };
    }

    private static String prettyLevel(SecurityLevel lvl) {
        if (lvl == null) return "?";
        return lvl == SecurityLevel.SECRET ? "Sec" : "Pub";
    }

    private static String prettyRecord(Map<String, Type> fields) {
        if (fields == null || fields.isEmpty()) {
            return "{}";
        }

        List<Map.Entry<String, Type>> entries = new ArrayList<>(fields.entrySet());
        entries.sort(Map.Entry.comparingByKey());

        StringBuilder sb = new StringBuilder();
        sb.append("{");
        for (int i = 0; i < entries.size(); i++) {
            Map.Entry<String, Type> e = entries.get(i);
            if (i > 0) sb.append(", ");
            sb.append(e.getKey()).append(": ").append(pretty(e.getValue(), 0));
        }
        sb.append("}");
        return sb.toString();
    }
}
