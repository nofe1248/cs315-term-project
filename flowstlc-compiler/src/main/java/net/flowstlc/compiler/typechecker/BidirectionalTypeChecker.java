package net.flowstlc.compiler.typechecker;

import net.flowstlc.compiler.ast.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public final class BidirectionalTypeChecker {
    private static final class InferResult {
        final Type type;
        final UsageContext usage;

        InferResult(Type type, UsageContext usage) {
            this.type = type;
            this.usage = usage;
        }
    }

    public void checkProgram(Program program, String entryPoint) {
        Objects.requireNonNull(program, "program");
        Objects.requireNonNull(entryPoint, "entryPoint");

        // Collect declared names so we can synthesize their types.
        TypeEnv env = new TypeEnv();
        for (Declaration d : program.getDeclarations()) {
            if (d instanceof FunctionDeclaration fd) {
                env = env.extend(fd.getName(), fd.getType());
            } else if (d instanceof ConstantDeclaration cd) {
                env = env.extend(cd.getName(), cd.getType());
            }
        }

        // Entry point must exist and be a function.
        Type entryTy = env.lookupVar(entryPoint);
        if (entryTy == null) {
            throw new TypeError("Unknown entry point: " + entryPoint);
        }
        requireFunctionType(entryTy, "Entry point '" + entryPoint + "' is not a function");

        for (Declaration d : program.getDeclarations()) {
            if (d instanceof ConstantDeclaration cd) {
                check(env, cd.getValue(), cd.getType());
            } else if (d instanceof FunctionDeclaration fd) {
                checkFunctionDeclaration(env, fd);
            }
        }
    }

    private UsageContext check(TypeEnv env, Expr expr, Type expected) {
        Objects.requireNonNull(env, "env");
        Objects.requireNonNull(expr, "expr");
        Objects.requireNonNull(expected, "expected");

        // BD-Pro: If we can check t against type T, we can also create a modality [t] and scale the usage with grade r.
        if (expr instanceof ModalityExpr me) {
            if (expected instanceof ModalityType mt) {
                Expr innerExpr = me.getInner();
                UsageContext innerUsage = check(env, innerExpr, mt.getInner());
                return innerUsage.contextScale(mt.getLevel());
            } else {
                throw new TypeError("Expected modality type for expression, found: " + prettyType(expected));
            }
        }

        // BD-Let: For an expression let [x] = t1 in t2, infer t1 (a modality) to get type and usage Delta1,
        // and check the body t2 in an extended environment with x : T and get usage Delta2.
        // We then check if the calculated usage of x in Delta2 is <= the grade r from the modality type.
        // If so, we return Delta1 + (Delta2 without x).
        if (expr instanceof LetExpr letExpr) {
            Expr boundExpr = letExpr.getBound();
            String varName = letExpr.getName();
            Expr bodyExpr = letExpr.getInExpr();

            // Infer the bound expression to get its type and usage.
            InferResult boundResult = infer(env, boundExpr);
            Type boundType = boundResult.type;
            UsageContext boundUsage = boundResult.usage;

            if (!(boundType instanceof ModalityType mt)) {
                throw new TypeError("Let-bound expression must have a modality type, found: " + prettyType(boundType));
            }

            TypeEnv extendedEnv = env.extend(varName, mt.getInner());
            UsageContext bodyUsage = check(extendedEnv, bodyExpr, expected);

            // Ensure the usage of the bound variable in the body is within the allowed grade.
            SecurityLevel usedLevel = bodyUsage.getUsageOrDefault(varName, SecurityOps.top());
            if (!SecurityOps.leq(mt.getLevel(), usedLevel)) {
                throw new TypeError("In let-binding: variable '" + varName + "' used at " + prettyLevel(usedLevel)
                        + " which is not > declared modality grade " + prettyLevel(mt.getLevel()));
            }

            // Combine usages: remove the bound variable from body usage and add bound usage.
            bodyUsage.deleteUsage(varName);
            return boundUsage.contextAdd(bodyUsage);
        }

        // BD-Record: If for each i, we can check ti against Ti and produce usage Delta_i,
        // then we can check the record {f1 = t1, ..., fn = tn} against type {f1 : T1, ..., fn : Tn}
        // and produce usage sum_i Delta_i.
        if (expr instanceof RecordExpr recExpr) {
            if (expected instanceof RecordType recType) {
                final UsageContext[] totalUsage = {new UsageContext()};
                recExpr.getFields().forEach((name, fieldExpr) -> {
                    Type fieldExpectedType = recType.getFields().get(name);
                    if (fieldExpectedType == null) {
                        throw new TypeError("Record field '" + name + "' not found in expected type");
                    }
                    UsageContext fieldUsage = check(env, fieldExpr, fieldExpectedType);
                    totalUsage[0] = totalUsage[0].contextAdd(fieldUsage);
                });
                return totalUsage[0];
            } else {
                throw new TypeError("Expected record type for record expression, found: " + prettyType(expected));
            }
        }

        // BD-Cond: If we can check the condition against Bool, and check both branches against T,
        // we can check the whole if-expression against T, joining usages from all three sub-expressions.
        if (expr instanceof IfExpr ifExpr) {
            UsageContext condUsage = check(env, ifExpr.getCondition(), new BuiltinType(BuiltinKind.BOOL));
            UsageContext thenUsage = check(env, ifExpr.getThenBranch(), expected);
            UsageContext elseUsage = check(env, ifExpr.getElseBranch(), expected);

            // Combine usages from condition, then-branch, and else-branch
            return condUsage.contextAdd(thenUsage).contextAdd(elseUsage);
        }

        // BD-Switch: If we can synthesize a type for t, we can check it against the same type.
        InferResult got = infer(env, expr);
        requireTypeEquals(got.type, expected);
        return got.usage;
    }

    private InferResult infer(TypeEnv env, Expr expr) {
        Objects.requireNonNull(env, "env");
        Objects.requireNonNull(expr, "expr");

        // BD-Var: lookup in the typing context, generate usage PUBLIC for that variable.
        if (expr instanceof IdentifierExpr id) {
            Type bindingTy = env.lookupVar(id.getName());
            if (bindingTy == null) {
                throw new TypeError("Unbound variable: " + id.getName());
            }

            UsageContext u = new UsageContext();
            u.addUsage(id.getName(), SecurityOps.semiringOne()); // PUBLIC
            return new InferResult(bindingTy, u);
        }

        // BD-App: synthesize function type, check arg, scale arg usage by input grade r.
        if (expr instanceof FunctionCallExpr call) {
            InferResult funRes = inferFunctionName(env, call.getFunctionName());

            Type funTy = funRes.type;
            UsageContext usage = funRes.usage;

            for (Expr arg : call.getArguments()) {
                if (funTy instanceof FunctionType ft) {
                    UsageContext uArg = check(env, arg, ft.getFrom());
                    uArg = uArg.contextScale(ft.getLevel());
                    usage = usage.contextAdd(uArg);
                    funTy = ft.getTo();
                } else {
                    throw new TypeError("Attempted to apply non-function type: " + prettyType(funTy));
                }
            }

            return new InferResult(funTy, usage);
        }

        // BD-Proj: If we can synthesize a record type for t, we can project field fi to get type Ti.
        if (expr instanceof RecordFieldAccessExpr proj) {
            InferResult recRes = infer(env, proj.getRecordExpr());
            Type recTy = recRes.type;
            UsageContext usage = recRes.usage;

            if (recTy instanceof RecordType rt) {
                Type fieldTy = rt.getFields().get(proj.getFieldName());
                if (fieldTy == null) {
                    throw new TypeError("Field '" + proj.getFieldName() + "' not found in record type");
                }
                return new InferResult(fieldTy, usage);
            } else {
                throw new TypeError("Attempted to project field from non-record type: " + prettyType(recTy));
            }
        }

        // BD-True/BD-False: synthesize types for boolean literals with no usage.
        if (expr instanceof BoolLiteralExpr literal) {
            Type boolType = new BuiltinType(BuiltinKind.BOOL);
            return new InferResult(boolType, new UsageContext());
        }

        // BD-Zero/BD-Succ/BD-Pred: synthesize types for natural number literals with no usage.
        if (expr instanceof IntLiteralExpr natLiteral) {
            Type intType = new BuiltinType(BuiltinKind.INT);
            return new InferResult(intType, new UsageContext());
        }

        // (no corresponding rule in the spec): synthesize type for string literal with no usage.
        if (expr instanceof StringLiteralExpr strLiteral) {
            Type stringType = new BuiltinType(BuiltinKind.STRING);
            return new InferResult(stringType, new UsageContext());
        }

        // BD-Unit: synthesize type for unit literal with no usage.
        if (expr instanceof UnitLiteralExpr unitLiteral) {
            Type unitType = new BuiltinType(BuiltinKind.UNIT);
            return new InferResult(unitType, new UsageContext());
        }

        // (no corresponding rule in the spec): check the argument's types, then synthesize the type
        // for intrinsic function calls.
        if (expr instanceof IntrinsicExpr intrinsicCall) {
            String name = intrinsicCall.getIntrinsicName();
            List<Expr> args = intrinsicCall.getArguments();

            final UsageContext[] usageRef = {new UsageContext()};

            // Allow either a raw builtin type or a modality-wrapped builtin type.
            // This matches the interpreter, where the label filter erases modality at runtime.
            java.util.function.BiConsumer<Expr, BuiltinKind> checkBuiltinOrModality = (argExpr, kind) -> {
                Type builtin = new BuiltinType(kind);
                try {
                    UsageContext u = check(env, argExpr, builtin);
                    usageRef[0] = usageRef[0].contextAdd(u);
                    return;
                } catch (TypeError ignored) {
                    // fall through
                }
                Type mod = new ModalityType(builtin, SecurityOps.semiringOne());
                UsageContext u = check(env, argExpr, mod);
                usageRef[0] = usageRef[0].contextAdd(u);
            };

            switch (name) {
                case "printInt" -> {
                    if (args.size() != 1) {
                        throw new TypeError("printInt expects 1 argument, got " + args.size());
                    }
                    checkBuiltinOrModality.accept(args.get(0), BuiltinKind.INT);
                    return new InferResult(new BuiltinType(BuiltinKind.UNIT), usageRef[0]);
                }
                case "printBool" -> {
                    if (args.size() != 1) {
                        throw new TypeError("printBool expects 1 argument, got " + args.size());
                    }
                    checkBuiltinOrModality.accept(args.get(0), BuiltinKind.BOOL);
                    return new InferResult(new BuiltinType(BuiltinKind.UNIT), usageRef[0]);
                }
                case "printString" -> {
                    if (args.size() != 1) {
                        throw new TypeError("printString expects 1 argument, got " + args.size());
                    }
                    checkBuiltinOrModality.accept(args.get(0), BuiltinKind.STRING);
                    return new InferResult(new BuiltinType(BuiltinKind.UNIT), usageRef[0]);
                }

                case "readInt" -> {
                    if (!args.isEmpty()) {
                        throw new TypeError("readInt expects 0 arguments, got " + args.size());
                    }
                    return new InferResult(new BuiltinType(BuiltinKind.INT), usageRef[0]);
                }
                case "readBool" -> {
                    if (!args.isEmpty()) {
                        throw new TypeError("readBool expects 0 arguments, got " + args.size());
                    }
                    return new InferResult(new BuiltinType(BuiltinKind.BOOL), usageRef[0]);
                }
                case "readString" -> {
                    if (!args.isEmpty()) {
                        throw new TypeError("readString expects 0 arguments, got " + args.size());
                    }
                    return new InferResult(new BuiltinType(BuiltinKind.STRING), usageRef[0]);
                }

                case "printf" -> {
                    // Variadic type can't be represented precisely. We enforce the runtime contract:
                    //  - at least 1 argument
                    //  - first argument is String (or [String])
                    //  - remaining arguments are Int/Bool/String/Unit (optionally modality-wrapped)
                    if (args.isEmpty()) {
                        throw new TypeError("printf expects at least 1 argument");
                    }
                    checkBuiltinOrModality.accept(args.get(0), BuiltinKind.STRING);
                    for (int i = 1; i < args.size(); i++) {
                        Expr a = args.get(i);
                        // Try each supported kind.
                        boolean ok = false;
                        for (BuiltinKind k : new BuiltinKind[]{BuiltinKind.INT, BuiltinKind.BOOL, BuiltinKind.STRING, BuiltinKind.UNIT}) {
                            try {
                                UsageContext u = check(env, a, new BuiltinType(k));
                                usageRef[0] = usageRef[0].contextAdd(u);
                                ok = true;
                                break;
                            } catch (TypeError ignored) {
                                // try next
                            }
                            try {
                                UsageContext u = check(env, a, new ModalityType(new BuiltinType(k), SecurityOps.semiringOne()));
                                usageRef[0] = usageRef[0].contextAdd(u);
                                ok = true;
                                break;
                            } catch (TypeError ignored) {
                                // try next
                            }
                        }
                        if (!ok) {
                            throw new TypeError("printf format argument #" + i + " must be Int/Bool/String/Unit (optionally modality-wrapped)");
                        }
                    }
                    return new InferResult(new BuiltinType(BuiltinKind.UNIT), usageRef[0]);
                }
                case "format" -> {
                    if (args.isEmpty()) {
                        throw new TypeError("format expects at least 1 argument");
                    }
                    checkBuiltinOrModality.accept(args.get(0), BuiltinKind.STRING);
                    for (int i = 1; i < args.size(); i++) {
                        Expr a = args.get(i);
                        boolean ok = false;
                        for (BuiltinKind k : new BuiltinKind[]{BuiltinKind.INT, BuiltinKind.BOOL, BuiltinKind.STRING, BuiltinKind.UNIT}) {
                            try {
                                UsageContext u = check(env, a, new BuiltinType(k));
                                usageRef[0] = usageRef[0].contextAdd(u);
                                ok = true;
                                break;
                            } catch (TypeError ignored) {
                                // try next
                            }
                            try {
                                UsageContext u = check(env, a, new ModalityType(new BuiltinType(k), SecurityOps.semiringOne()));
                                usageRef[0] = usageRef[0].contextAdd(u);
                                ok = true;
                                break;
                            } catch (TypeError ignored) {
                                // try next
                            }
                        }
                        if (!ok) {
                            throw new TypeError("format format argument #" + i + " must be Int/Bool/String/Unit (optionally modality-wrapped)");
                        }
                    }
                    return new InferResult(new BuiltinType(BuiltinKind.STRING), usageRef[0]);
                }

                default -> throw new TypeError("Unknown intrinsic: " + name);
            }
        }

        // arithmetic, comparison, logical: check operand types forced by operator,
        // synthesize result type, and add operand usages.
        if (expr instanceof UnaryExpr unaryExpr) {
            BuiltinType intTy = new BuiltinType(BuiltinKind.INT);
            BuiltinType boolTy = new BuiltinType(BuiltinKind.BOOL);

            return switch (unaryExpr.getOp()) {
                case NEG -> {
                    UsageContext u = check(env, unaryExpr.getExpr(), intTy);
                    yield new InferResult(intTy, u);
                }
                case NOT -> {
                    UsageContext u = check(env, unaryExpr.getExpr(), boolTy);
                    yield new InferResult(boolTy, u);
                }
            };
        }

        if (expr instanceof BinaryExpr binaryExpr) {
            BuiltinType intTy = new BuiltinType(BuiltinKind.INT);
            BuiltinType boolTy = new BuiltinType(BuiltinKind.BOOL);

            BinaryOp op = binaryExpr.getOp();

            // All binary ops in this language are fixed to either Int or Bool operands.
            Type operandTy;
            Type resultTy;

            switch (op) {
                // Int -> Int -> Int
                case ADD, SUB, MUL, DIV, MOD -> {
                    operandTy = intTy;
                    resultTy = intTy;
                }
                // Bool -> Bool -> Bool
                case AND, OR -> {
                    operandTy = boolTy;
                    resultTy = boolTy;
                }
                // Int -> Int -> Bool
                case EQ, NEQ, LT, LTE, GT, GTE -> {
                    operandTy = intTy;
                    resultTy = boolTy;
                }
                default -> throw new TypeError("Unknown binary operator: " + op);
            }

            UsageContext uLeft = check(env, binaryExpr.getLeft(), operandTy);
            UsageContext uRight = check(env, binaryExpr.getRight(), operandTy);
            return new InferResult(resultTy, uLeft.contextAdd(uRight));
        }

        // BD-Seq: If we can synthesize a type for t, we can check it against the same type.
        if (expr instanceof SequenceExpr seqExpr) {
            InferResult firstRes = infer(env, seqExpr.getFirst());
            InferResult secondRes = infer(env, seqExpr.getSecond());
            return new InferResult(secondRes.type, firstRes.usage.contextAdd(secondRes.usage));
        }

        throw new TypeError("No bidirectional synthesis rule implemented for expression: " + expr.getClass().getSimpleName());
    }

    private InferResult inferFunctionName(TypeEnv env, String functionName) {
        Type bindingTy = env.lookupVar(functionName);
        if (bindingTy == null) {
            throw new TypeError("Unknown function: " + functionName);
        }
        UsageContext u = new UsageContext();
        u.addUsage(functionName, SecurityOps.semiringOne());
        return new InferResult(bindingTy, u);
    }

    /**
     * BD-Abs: for `fun f x1 x2 ... = body` with declared type
     * `T1 ^r1 -> T2 ^r2 -> ... -> Tret`, check the body against Tret and ensure each parameter's
     * computed usage is <= the corresponding arrow grade r.
     */
    private void checkFunctionDeclaration(TypeEnv topEnv, FunctionDeclaration fd) {
        Type declared = fd.getType();
        List<String> params = fd.getParameters();

        int syntacticArity = params.size();
        int declaredArity = functionTypeArity(declared);

        // Allow the common surface-syntax sugar:
        //   fun main : Unit^Pub -> T
        //   fun main = body
        // i.e., a nullary definition for a unary Unit-argument function.
        boolean allowImplicitUnitParam = syntacticArity == 0
                && declaredArity == 1
                && isUnitType(getNthFunctionInputType(declared, 0));

        int arityForChecking = syntacticArity;
        if (allowImplicitUnitParam) {
            arityForChecking = 1;
        }

        if (!allowImplicitUnitParam) {
            if (syntacticArity > declaredArity) {
                throw new TypeError("Cannot check function '" + fd.getName() + "': declared type has arity "
                        + declaredArity + " but definition has " + syntacticArity + " parameter(s)");
            }
            if (syntacticArity == 0 && declaredArity > 0) {
                throw new TypeError("Cannot check function '" + fd.getName() + "': declared type expects "
                        + declaredArity + " argument(s) but definition has no parameters. "
                        + "If you intended a nullary function, use a non-function type; "
                        + "if you intended a thunk, use Unit as the argument type.");
            }
        }

        DecomposedFunType dec;
        if (arityForChecking == 0) {
            // Not a function type at all (or nullary definition). Just check body against declared type.
            dec = new DecomposedFunType(List.of(), List.of(), SecurityOps.semiringOne(), declared);
        } else {
            dec = decomposeFunctionType(declared, arityForChecking, "function '" + fd.getName() + "'");
        }

        TypeEnv env = topEnv;

        if (allowImplicitUnitParam) {
            // Synthesize a fresh, unnameable parameter so the body is checked under the right environment.
            // Using a hard-to-type name reduces risk of accidental collisions.
            env = env.extend("$unit", dec.paramTypes.get(0));
        } else {
            for (int i = 0; i < params.size(); i++) {
                env = env.extend(params.get(i), dec.paramTypes.get(i));
            }
        }

        UsageContext bodyUsage = check(env, fd.getBody(), dec.returnType);

        // Enforce: ri <= usage(xi) for each parameter.
        if (allowImplicitUnitParam) {
            SecurityLevel used = bodyUsage.getUsageOrDefault("$unit", SecurityOps.top());
            SecurityLevel allowed = dec.paramGrades.get(0);
            if (!SecurityOps.leq(allowed, used)) {
                throw new TypeError("In " + fd.getName() + ": implicit Unit parameter used at " + prettyLevel(used)
                        + " which is not > declared input grade " + prettyLevel(allowed));
            }
        } else {
            for (int i = 0; i < params.size(); i++) {
                String x = params.get(i);
                SecurityLevel used = bodyUsage.getUsageOrDefault(x, SecurityOps.top());
                SecurityLevel allowed = dec.paramGrades.get(i);
                if (!SecurityOps.leq(allowed, used)) {
                    throw new TypeError("In " + fd.getName() + ": parameter '" + x + "' used at " + prettyLevel(used)
                            + " which is not > declared input grade " + prettyLevel(allowed));
                }
            }
        }
    }

    private static final class DecomposedFunType {
        final List<Type> paramTypes;
        final List<SecurityLevel> paramGrades;
        final SecurityLevel inputGrade;
        final Type returnType;

        private DecomposedFunType(List<Type> paramTypes, List<SecurityLevel> paramGrades, SecurityLevel inputGrade, Type returnType) {
            this.paramTypes = paramTypes;
            this.paramGrades = paramGrades;
            this.inputGrade = inputGrade;
            this.returnType = returnType;
        }
    }

    private static DecomposedFunType decomposeFunctionType(Type ty, int arity, String where) {
        List<Type> paramTypes = new ArrayList<>();
        List<SecurityLevel> paramGrades = new ArrayList<>();

        Type cur = ty;
        for (int i = 0; i < arity; i++) {
            if (cur instanceof FunctionType ft) {
                paramTypes.add(ft.getFrom());
                paramGrades.add(ft.getLevel());
                cur = ft.getTo();
            } else if (cur instanceof UnannotatedFunctionType) {
                throw new TypeError("Cannot check " + where + ": unannotated function type doesn't provide input grade annotations");
            } else {
                throw new TypeError("Cannot check " + where + ": expected a function type with at least " + arity + " arguments");
            }
        }

        SecurityLevel inputGrade = (ty instanceof FunctionType ft) ? ft.getLevel() : SecurityOps.semiringOne();
        return new DecomposedFunType(paramTypes, paramGrades, inputGrade, cur);
    }

    private static int functionTypeArity(Type ty) {
        int n = 0;
        Type cur = ty;
        while (cur instanceof FunctionType ft) {
            n++;
            cur = ft.getTo();
        }
        while (cur instanceof UnannotatedFunctionType uft) {
            n++;
            cur = uft.getTo();
        }
        return n;
    }

    private static Type getNthFunctionInputType(Type ty, int indexZeroBased) {
        int i = 0;
        Type cur = ty;
        while (true) {
            if (cur instanceof FunctionType ft) {
                if (i == indexZeroBased) return ft.getFrom();
                i++;
                cur = ft.getTo();
                continue;
            }
            if (cur instanceof UnannotatedFunctionType uft) {
                if (i == indexZeroBased) return uft.getFrom();
                i++;
                cur = uft.getTo();
                continue;
            }
            return null;
        }
    }

    private static boolean isUnitType(Type ty) {
        return ty instanceof BuiltinType bt && bt.getKind() == BuiltinKind.UNIT;
    }

    private static void requireTypeEquals(Type got, Type expected) {
        if (!typeEquals(got, expected)) {
            throw new TypeError("Type mismatch: expected " + prettyType(expected) + ", got " + prettyType(got));
        }
    }

    private static void requireFunctionType(Type ty, String message) {
        if (ty instanceof FunctionType || ty instanceof UnannotatedFunctionType) {
            return;
        }
        throw new TypeError(message + " (found " + ty.getClass().getSimpleName() + ")");
    }

    private static boolean typeEquals(Type a, Type b) {
        if (a == b) return true;
        if (a == null || b == null) return false;

        if (a instanceof BuiltinType ba && b instanceof BuiltinType bb) {
            return ba.getKind() == bb.getKind();
        }

        if (a instanceof FunctionType fa && b instanceof FunctionType fb) {
            return typeEquals(fa.getFrom(), fb.getFrom())
                    && fa.getLevel() == fb.getLevel()
                    && typeEquals(fa.getTo(), fb.getTo());
        }

        if (a instanceof UnannotatedFunctionType ua && b instanceof UnannotatedFunctionType ub) {
            return typeEquals(ua.getFrom(), ub.getFrom()) && typeEquals(ua.getTo(), ub.getTo());
        }

        if (a instanceof ModalityType ma && b instanceof ModalityType mb) {
            return typeEquals(ma.getInner(), mb.getInner()) && ma.getLevel() == mb.getLevel();
        }

        return false;
    }

    private static String prettyType(Type ty) {
        if (ty == null) return "<null>";
        if (ty instanceof BuiltinType bt) return bt.getKind().name();
        if (ty instanceof FunctionType ft) {
            return "(" + prettyType(ft.getFrom()) + " ^" + prettyLevel(ft.getLevel()) + " -> " + prettyType(ft.getTo()) + ")";
        }
        if (ty instanceof UnannotatedFunctionType uft) {
            return "(" + prettyType(uft.getFrom()) + " -> " + prettyType(uft.getTo()) + ")";
        }
        if (ty instanceof ModalityType mt) {
            return prettyType(mt.getInner()) + " [" + prettyLevel(mt.getLevel()) + "]";
        }
        return ty.getClass().getSimpleName();
    }

    private static String prettyLevel(SecurityLevel lvl) {
        return lvl == SecurityLevel.SECRET ? "Sec" : "Pub";
    }
}
