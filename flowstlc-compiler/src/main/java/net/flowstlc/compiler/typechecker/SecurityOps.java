package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.ast.SecurityLevel;

public final class SecurityOps {
    private SecurityOps() {
    }

    public static boolean leq(SecurityLevel a, SecurityLevel b) {
        if (a == b) return true;
        return a == SecurityLevel.PUBLIC && b == SecurityLevel.SECRET;
    }

    public static SecurityLevel plus(SecurityLevel a, SecurityLevel b) {
        if (a == SecurityLevel.SECRET && b == SecurityLevel.SECRET) return SecurityLevel.SECRET;
        return SecurityLevel.PUBLIC;
    }

    public static SecurityLevel times(SecurityLevel a, SecurityLevel b) {
        if (a == SecurityLevel.PUBLIC || b == SecurityLevel.PUBLIC) return SecurityLevel.PUBLIC;
        return SecurityLevel.SECRET;
    }

    public static SecurityLevel bottom() {
        return SecurityLevel.PUBLIC;
    }

    public static SecurityLevel top() {
        return SecurityLevel.SECRET;
    }

    public static SecurityLevel semiringZero() {
        return SecurityLevel.SECRET;
    }

    public static SecurityLevel semiringOne() {
        return SecurityLevel.PUBLIC;
    }
}


