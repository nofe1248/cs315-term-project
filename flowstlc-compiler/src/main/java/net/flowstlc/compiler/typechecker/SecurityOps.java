package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.ast.SecurityLevel;

public final class SecurityOps {
    private SecurityOps() {
    }

    // a ⊑ b where PUBLIC ⊑ SECURE
    public static boolean leq(SecurityLevel a, SecurityLevel b) {
        if (a == b) return true;
        return a == SecurityLevel.PUBLIC && b == SecurityLevel.SECRET;
    }

    // addition as meet
    public static SecurityLevel plus(SecurityLevel a, SecurityLevel b) {
        if (a == SecurityLevel.SECRET && b == SecurityLevel.SECRET) return SecurityLevel.SECRET;
        return SecurityLevel.PUBLIC;
    }

    // multiplication as join
    public static SecurityLevel times(SecurityLevel a, SecurityLevel b) {
        if (a == SecurityLevel.SECRET || b == SecurityLevel.SECRET) return SecurityLevel.SECRET;
        return SecurityLevel.PUBLIC;
    }
}


