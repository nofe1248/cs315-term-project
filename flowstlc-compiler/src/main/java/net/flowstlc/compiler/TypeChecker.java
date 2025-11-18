package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.*;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static net.flowstlc.compiler.SecurityOps.leq;

public final class TypeChecker extends BaseASTVisitor<Type> {
    private final Map<String, FunctionType> functionTypes = new HashMap<>();
    private final Map<String, Type> constantTypes = new HashMap<>();

    private TypeEnv env = new TypeEnv();
    private SecurityLevel requiredGrade = SecurityLevel.SECRET;

    public void checkProgram(Program program, String entryPoint) {
        for (Declaration decl : program.getDeclarations()) {
            if (decl instanceof FunctionDeclaration fd) {
                if (!(fd.getType() instanceof FunctionType)) {
                    throw new TypeError("Function " + fd.getName() + " must have a function type");
                }
                functionTypes.put(fd.getName(), (FunctionType) fd.getType());
            } else if (decl instanceof ConstantDeclaration cd) {
                constantTypes.put(cd.getName(), cd.getType());
            }
        }

        for (Declaration decl : program.getDeclarations()) {
            if (decl instanceof ConstantDeclaration cd) {
                checkConstant(cd);
            }
        }

        for (Declaration decl : program.getDeclarations()) {
            if (decl instanceof FunctionDeclaration fd) {
                checkFunction(fd);
            }
        }

        FunctionType mainType = functionTypes.get(entryPoint);
        if (mainType == null) {
            throw new TypeError(String.format("Function entry point %s not found", entryPoint));
        }

        if (!(mainType.getFrom() instanceof BuiltinType bt && bt.getKind() == BuiltinKind.UNIT
                && mainType.getTo() instanceof BuiltinType bt2 && bt2.getKind() == BuiltinKind.INT
                && (mainType.getLevel() == SecurityLevel.SECRET || mainType.getLevel() == SecurityLevel.PUBLIC))) {
            throw new TypeError(String.format("Entry point function %s must have type Unit^Sec -> Int or Unit^Pub -> Int", entryPoint));
        }
    }

    private void checkConstant(ConstantDeclaration cd) {
        Type expected = cd.getType();
        Type actual = checkExpr(cd.getValue(), new TypeEnv(), SecurityLevel.SECRET);
        if (!typeEquals(expected, actual)) {
            throw new TypeError(String.format("Constant '%s' has type %s but expected %s",
                    cd.getName(), showType(actual), showType(expected)));
        }
    }

    private void checkFunction(FunctionDeclaration fd) {
        Type declaredType = fd.getType();
        if (!(declaredType instanceof FunctionType outerFt)) {
            throw new TypeError("Function '" + fd.getName() + "' must have a function type");
        }
        Type returnType = outerFt.getTo();

        int paramCount = fd.getParameters().size();
        Type[] paramTypes = new Type[paramCount];
        SecurityLevel[] paramGrades = new SecurityLevel[paramCount];

        Type current = declaredType;
        for (int i = 0; i < paramCount; i++) {
            if (!(current instanceof FunctionType ft)) {
                throw new TypeError("Function '" + fd.getName() + "' expected to have " + paramCount
                        + " parameters, but type has fewer arrows");
            }
            paramTypes[i] = ft.getFrom();
            paramGrades[i] = ft.getLevel();
            current = ft.getTo();
        }

        TypeEnv localEnv = new TypeEnv();
        for (int i = 0; i < paramCount; i++) {
            String name = fd.getParameters().get(i);
            localEnv = localEnv.extend(name, paramTypes[i], paramGrades[i]);
        }
        for (Map.Entry<String, Type> e : constantTypes.entrySet()) {
            localEnv = localEnv.extend(e.getKey(), e.getValue(), SecurityLevel.SECRET);
        }

        Type bodyType = checkExpr(fd.getBody(), localEnv, SecurityLevel.SECRET);
        if (!typeEquals(returnType, bodyType)) {
            throw new TypeError("Function '" + fd.getName() + "' body has type " + showType(bodyType)
                    + " but expected " + showType(returnType));
        }
    }

    public Type checkExpr(Expr expr, TypeEnv env, SecurityLevel requiredGrade) {
        TypeEnv oldEnv = this.env;
        SecurityLevel oldReq = this.requiredGrade;
        try {
            this.env = env;
            this.requiredGrade = requiredGrade;
            return expr.accept(this);
        } finally {
            this.env = oldEnv;
            this.requiredGrade = oldReq;
        }
    }

    // ==================== Expression visitors ====================

    @Override
    public Type visitIntLiteralExpr(IntLiteralExpr expr) {
        return new BuiltinType(BuiltinKind.INT);
    }

    @Override
    public Type visitBoolLiteralExpr(BoolLiteralExpr expr) {
        return new BuiltinType(BuiltinKind.BOOL);
    }

    @Override
    public Type visitUnitLiteralExpr(UnitLiteralExpr expr) {
        return new BuiltinType(BuiltinKind.UNIT);
    }

    @Override
    public Type visitIdentifierExpr(IdentifierExpr expr) {
        String name = expr.getName();
        TypeEnv.VarBinding binding = env.lookupVar(name);
        if (binding != null) {
            if (!leq(requiredGrade, binding.grade)) {
                throw new TypeError("Using variable '" + name + "' at grade " + requiredGrade
                        + " requires grade " + binding.grade);
            }
            return binding.type;
        }
        Type constType = constantTypes.get(name);
        if (constType != null) {
            // constants treated as SECURE
            if (!leq(requiredGrade, SecurityLevel.SECRET)) {
                throw new TypeError("Using constant '" + name + "' violates security grade");
            }
            return constType;
        }
        throw new TypeError("Unbound identifier '" + name + "'");
    }

    @Override
    public Type visitBinaryExpr(BinaryExpr expr) {
        Type leftType = checkExpr(expr.getLeft(), env, requiredGrade);
        Type rightType = checkExpr(expr.getRight(), env, requiredGrade);
        BinaryOp op = expr.getOp();
        return switch (op) {
            case ADD, SUB, MUL, DIV, MOD -> {
                requireInt(leftType, "left operand of " + op);
                requireInt(rightType, "right operand of " + op);
                yield new BuiltinType(BuiltinKind.INT);
            }
            case AND, OR -> {
                requireBool(leftType, "left operand of " + op);
                requireBool(rightType, "right operand of " + op);
                yield new BuiltinType(BuiltinKind.BOOL);
            }
            case EQ, NEQ -> {
                if (!typeEquals(leftType, rightType)) {
                    throw new TypeError("Operands of " + op + " must have same type, got "
                            + showType(leftType) + " and " + showType(rightType));
                }
                yield new BuiltinType(BuiltinKind.BOOL);
            }
            case LT, LTE, GT, GTE -> {
                requireInt(leftType, "left operand of " + op);
                requireInt(rightType, "right operand of " + op);
                yield new BuiltinType(BuiltinKind.BOOL);
            }
        };
    }

    @Override
    public Type visitUnaryExpr(UnaryExpr expr) {
        Type inner = checkExpr(expr.getExpr(), env, requiredGrade);
        return switch (expr.getOp()) {
            case NOT -> {
                requireBool(inner, "operand of NOT");
                yield new BuiltinType(BuiltinKind.BOOL);
            }
            case NEG -> {
                requireInt(inner, "operand of NEG");
                yield new BuiltinType(BuiltinKind.INT);
            }
        };
    }

    @Override
    public Type visitIfExpr(IfExpr expr) {
        Type condType = checkExpr(expr.getCondition(), env, SecurityLevel.PUBLIC);
        requireBool(condType, "condition of if");
        Type thenType = checkExpr(expr.getThenBranch(), env, requiredGrade);
        Type elseType = checkExpr(expr.getElseBranch(), env, requiredGrade);
        if (!typeEquals(thenType, elseType)) {
            throw new TypeError("Branches of if must have same type, got "
                    + showType(thenType) + " and " + showType(elseType));
        }
        return thenType;
    }

    @Override
    public Type visitLetExpr(LetExpr expr) {
        Type boundType = checkExpr(expr.getBound(), env, requiredGrade);
        if (!(boundType instanceof ModalityType mt)) {
            throw new TypeError("let-bound expression must have modality type, got " + showType(boundType));
        }
        TypeEnv extended = env.extend(expr.getName(), mt.getInner(), mt.getLevel());
        return checkExpr(expr.getInExpr(), extended, requiredGrade);
    }

    @Override
    public Type visitModalityExpr(ModalityExpr expr) {
        Type inner = checkExpr(expr.getInner(), env, requiredGrade);
        return new ModalityType(inner, requiredGrade);
    }

    @Override
    public Type visitFunctionCallExpr(FunctionCallExpr expr) {
        FunctionType fType = functionTypes.get(expr.getFunctionName());
        if (fType == null) {
            throw new TypeError("Call to unknown function '" + expr.getFunctionName() + "'");
        }
        List<Expr> args = expr.getArguments();
        Type current = fType;
        for (int i = 0; i < args.size(); i++) {
            if (!(current instanceof FunctionType ft)) {
                throw new TypeError("Too many arguments in call to '" + expr.getFunctionName() + "'");
            }
            Type argType = checkExpr(args.get(i), env, ft.getLevel());
            if (!typeEquals(argType, ft.getFrom())) {
                throw new TypeError("Argument " + (i + 1) + " of '" + expr.getFunctionName() + "' has type "
                        + showType(argType) + " but expected " + showType(ft.getFrom()));
            }
            current = ft.getTo();
        }
        return current;
    }

    // ==================== Type utilities ====================

    @Override
    public Type visitBuiltinType(BuiltinType expr) {
        return expr; // identity
    }

    @Override
    public Type visitFunctionType(FunctionType type) {
        return type;
    }

    @Override
    public Type visitModalityType(ModalityType type) {
        return type;
    }

    @Override
    public Type visitProgram(Program program) {
        return null;
    }

    @Override
    public Type visitConstantDeclaration(ConstantDeclaration declaration) {
        return null;
    }

    @Override
    public Type visitFunctionDeclaration(FunctionDeclaration declaration) {
        return null;
    }

    @Override
    public Type visitUnannotatedFunctionType(UnannotatedFunctionType type) {
        return type;
    }

    private void requireInt(Type type, String what) {
        if (!(type instanceof BuiltinType bt && bt.getKind() == BuiltinKind.INT)) {
            throw new TypeError(what + " must have type Int, got " + showType(type));
        }
    }

    private void requireBool(Type type, String what) {
        if (!(type instanceof BuiltinType bt && bt.getKind() == BuiltinKind.BOOL)) {
            throw new TypeError(what + " must have type Bool, got " + showType(type));
        }
    }

    private boolean typeEquals(Type a, Type b) {
        if (a == b) return true;
        if (a == null || b == null) return false;
        if (a.getClass() != b.getClass()) return false;
        if (a instanceof BuiltinType btA && b instanceof BuiltinType btB) {
            return btA.getKind() == btB.getKind();
        }
        if (a instanceof FunctionType ftA && b instanceof FunctionType ftB) {
            return typeEquals(ftA.getFrom(), ftB.getFrom())
                    && ftA.getLevel() == ftB.getLevel()
                    && typeEquals(ftA.getTo(), ftB.getTo());
        }
        if (a instanceof ModalityType mtA && b instanceof ModalityType mtB) {
            return typeEquals(mtA.getInner(), mtB.getInner())
                    && mtA.getLevel() == mtB.getLevel();
        }
        if (a instanceof UnannotatedFunctionType uA && b instanceof UnannotatedFunctionType uB) {
            return typeEquals(uA.getFrom(), uB.getFrom()) && typeEquals(uA.getTo(), uB.getTo());
        }
        return false;
    }

    private String showType(Type t) {
        if (t instanceof BuiltinType bt) {
            return bt.getKind().name();
        }
        if (t instanceof FunctionType ft) {
            return showType(ft.getFrom()) + "^" + ft.getLevel() + "->" + showType(ft.getTo());
        }
        if (t instanceof ModalityType mt) {
            return showType(mt.getInner()) + " [" + mt.getLevel() + "]";
        }
        if (t instanceof UnannotatedFunctionType u) {
            return showType(u.getFrom()) + "->" + showType(u.getTo());
        }
        return t == null ? "<null>" : t.toString();
    }
}
