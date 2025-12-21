package net.flowstlc.compiler.lsp;

import net.flowstlc.compiler.ast.*;

public final class FlowstlcSymbols {
    private FlowstlcSymbols() {}

    public static String lookupTopLevelType(Program program, String name) {
        if (program == null || name == null) {
            return null;
        }
        for (Declaration d : program.getDeclarations()) {
            if (d instanceof FunctionDeclaration fd && name.equals(fd.getName())) {
                return TypePrettyPrinter.pretty(fd.getType());
            }
            if (d instanceof ConstantDeclaration cd && name.equals(cd.getName())) {
                return TypePrettyPrinter.pretty(cd.getType());
            }
        }
        return null;
    }
}
