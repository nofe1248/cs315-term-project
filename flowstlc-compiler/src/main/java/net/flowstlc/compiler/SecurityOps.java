package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.SecurityLevel;

public final class SecurityOps {
    private SecurityOps() {
    }

    // a ⊑ b where PUBLIC ⊑ SECURE
    public static boolean leq(SecurityLevel a, SecurityLevel b) {
        if (a == b) return true;
        return a == SecurityLevel.PUBLIC && b == SecurityLevel.SECURE;
    }

    // addition as meet
    public static SecurityLevel plus(SecurityLevel a, SecurityLevel b) {
        if (a == SecurityLevel.SECURE && b == SecurityLevel.SECURE) return SecurityLevel.SECURE;
        return SecurityLevel.PUBLIC;
    }

    // multiplication as join
    public static SecurityLevel times(SecurityLevel a, SecurityLevel b) {
        if (a == SecurityLevel.SECURE || b == SecurityLevel.SECURE) return SecurityLevel.SECURE;
        return SecurityLevel.PUBLIC;
    }
}


