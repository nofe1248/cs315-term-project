package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.ast.SecurityLevel;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public final class UsageContext {
    private final Map<String, SecurityLevel> usageMap;

    public UsageContext() {
        this.usageMap = new HashMap<>();
    }

    private UsageContext(Map<String, SecurityLevel> usageMap) {
        this.usageMap = usageMap;
    }

    public SecurityLevel getUsage(String varName) {
        return usageMap.get(varName);
    }

    public SecurityLevel getUsageOrDefault(String varName, SecurityLevel defaultLevel) {
        return usageMap.getOrDefault(varName, defaultLevel);
    }

    public void addUsage(String varName, SecurityLevel level) {
        usageMap.put(varName, level);
    }

    public void deleteUsage(String varName) {
        usageMap.remove(varName);
    }

    // Add two usage contexts according to the following specification:
    // If a variable appears in both contexts, takes the sum of their level.
    // If a variable appears in only one context, add its level with SECRET.
    public UsageContext contextAdd(UsageContext other) {
        Map<String, SecurityLevel> newMap = new HashMap<>();

        // Add variables from this context
        for (Map.Entry<String, SecurityLevel> entry : this.usageMap.entrySet()) {
            String varName = entry.getKey();
            SecurityLevel level1 = entry.getValue();
            SecurityLevel level2 = other.usageMap.getOrDefault(varName, SecurityLevel.SECRET);
            SecurityLevel combinedLevel = SecurityOps.plus(level1, level2);
            newMap.put(varName, combinedLevel);
        }

        // Add variables from the other context that are not in this context
        for (Map.Entry<String, SecurityLevel> entry : other.usageMap.entrySet()) {
            String varName = entry.getKey();
            if (!this.usageMap.containsKey(varName)) {
                SecurityLevel level2 = entry.getValue();
                SecurityLevel combinedLevel = SecurityOps.plus(SecurityLevel.SECRET, level2);
                newMap.put(varName, combinedLevel);
            }
        }

        return new UsageContext(newMap);
    }

    public UsageContext contextScale(SecurityLevel scaleLevel) {
        Map<String, SecurityLevel> newMap = new HashMap<>();
        for (Map.Entry<String, SecurityLevel> entry : this.usageMap.entrySet()) {
            String varName = entry.getKey();
            SecurityLevel originalLevel = entry.getValue();
            SecurityLevel scaledLevel = SecurityOps.times(originalLevel, scaleLevel);
            newMap.put(varName, scaledLevel);
        }
        return new UsageContext(newMap);
    }

    // Same as contextAdd but using times instead of plus
    public UsageContext contextJoin(UsageContext other) {
        Map<String, SecurityLevel> newMap = new HashMap<>();

        // Join variables from this context
        for (Map.Entry<String, SecurityLevel> entry : this.usageMap.entrySet()) {
            String varName = entry.getKey();
            SecurityLevel level1 = entry.getValue();
            SecurityLevel level2 = other.usageMap.getOrDefault(varName, SecurityLevel.SECRET);
            SecurityLevel combinedLevel = SecurityOps.times(level1, level2);
            newMap.put(varName, combinedLevel);
        }

        // Join variables from the other context that are not in this context
        for (Map.Entry<String, SecurityLevel> entry : other.usageMap.entrySet()) {
            String varName = entry.getKey();
            if (!this.usageMap.containsKey(varName)) {
                SecurityLevel level2 = entry.getValue();
                SecurityLevel combinedLevel = SecurityOps.times(SecurityLevel.SECRET, level2);
                newMap.put(varName, combinedLevel);
            }
        }

        return new UsageContext(newMap);
    }

    public static void printUsageContext(UsageContext context) {
        System.out.println("UsageContext:");
        for (Map.Entry<String, SecurityLevel> entry : context.usageMap.entrySet()) {
            System.out.println("  " + entry.getKey() + " : " + entry.getValue());
        }
    }
}
