package net.flowstlc.compiler.interpreter;

import net.flowstlc.compiler.ast.*;

import java.math.BigInteger;
import java.util.List;

public class EvalVisitor implements ASTVisitor<Value> {

    private Env env;

    public EvalVisitor(Env env) {
        this.env = env;
    }

    // ---------------- Program / Declarations ----------------

    @Override
    public Value visitProgram(Program program) {
        for (Declaration decl : program.getDeclarations()) {
            decl.accept(this);
        }
        return UnitV.INSTANCE;
    }

    @Override
    public Value visitConstantDeclaration(ConstantDeclaration declaration) {
        Value v = declaration.getValue().accept(this);
        env.put(declaration.getName(), v);
        return UnitV.INSTANCE;
    }

    @Override
    public Value visitFunctionDeclaration(FunctionDeclaration declaration) {
        ClosureV clo = new ClosureV(
                declaration.getParameters(),
                declaration.getBody(),
                env
        );
        env.put(declaration.getName(), clo);
        return UnitV.INSTANCE;
    }

    // ---------------- Literals ----------------

    @Override
    public Value visitIntLiteralExpr(IntLiteralExpr expr) {
        // IntLiteralExpr.getValue() : BigInteger
        return new IntV(expr.getValue());
    }

    @Override
    public Value visitBoolLiteralExpr(BoolLiteralExpr expr) {
        return new BoolV(expr.getValue());
    }

    @Override
    public Value visitUnitLiteralExpr(UnitLiteralExpr expr) {
        return UnitV.INSTANCE;
    }

    // ---------------- Variables / Control ----------------

    @Override
    public Value visitIdentifierExpr(IdentifierExpr expr) {
        return env.get(expr.getName());
    }

    @Override
    public Value visitLetExpr(LetExpr expr) {
        Value boundVal = expr.getBound().accept(this);

        Env oldEnv = env;
        Env newEnv = env.extend();
        newEnv.put(expr.getName(), boundVal);
        env = newEnv;

        Value result = expr.getInExpr().accept(this);
        env = oldEnv;
        return result;
    }

    @Override
    public Value visitIfExpr(IfExpr expr) {
        Value cond = expr.getCondition().accept(this);
        if (!(cond instanceof BoolV)) {
            throw new RuntimeError("Condition is not a boolean");
        }
        boolean b = ((BoolV) cond).getValue();
        return b
                ? expr.getThenBranch().accept(this)
                : expr.getElseBranch().accept(this);
    }

    // ---------------- Function call ----------------

    @Override
    public Value visitFunctionCallExpr(FunctionCallExpr expr) {
        // functionName is a String, lookup from env
        Value fun = env.get(expr.getFunctionName());
        if (!(fun instanceof ClosureV)) {
            throw new RuntimeError("Not a function: " + expr.getFunctionName());
        }
        ClosureV clo = (ClosureV) fun;

        List<String> params = clo.getParams();
        List<Expr> args = expr.getArguments();
        if (params.size() != args.size()) {
            throw new RuntimeError("Argument number mismatch for " + expr.getFunctionName()
                    + ": expected " + params.size() + " got " + args.size());
        }

        Env oldEnv = env;
        Env callEnv = clo.getEnv().extend();

        for (int i = 0; i < params.size(); i++) {
            Value argVal = args.get(i).accept(this);
            callEnv.put(params.get(i), argVal);
        }

        env = callEnv;
        Value result = clo.getBody().accept(this);
        env = oldEnv;
        return result;
    }

    // ---------------- Unary / Binary ----------------

    @Override
    public Value visitUnaryExpr(UnaryExpr expr) {
        Value v = expr.getExpr().accept(this);

        switch (expr.getOp()) {
            case NEG -> {
                if (!(v instanceof IntV)) {
                    throw new RuntimeError("NEG requires int");
                }
                IntV iv = (IntV) v;
                return new IntV(iv.getValue().negate());
            }
            case NOT -> {
                if (!(v instanceof BoolV)) {
                    throw new RuntimeError("NOT requires bool");
                }
                BoolV bv = (BoolV) v;
                return new BoolV(!bv.getValue());
            }
            default -> throw new RuntimeError("Unknown unary op: " + expr.getOp());
        }
    }

    @Override
    public Value visitBinaryExpr(BinaryExpr expr) {
        Value l = expr.getLeft().accept(this);
        Value r = expr.getRight().accept(this);

        switch (expr.getOp()) {

            case AND -> {
                if (!(l instanceof BoolV) || !(r instanceof BoolV)) {
                    throw new RuntimeError("AND expects bool");
                }
                return new BoolV(((BoolV) l).getValue() && ((BoolV) r).getValue());
            }

            case OR -> {
                if (!(l instanceof BoolV) || !(r instanceof BoolV)) {
                    throw new RuntimeError("OR expects bool");
                }
                return new BoolV(((BoolV) l).getValue() || ((BoolV) r).getValue());
            }

            default -> {
                if (!(l instanceof IntV) || !(r instanceof IntV)) {
                    throw new RuntimeError("Binary op expects int");
                }

                BigInteger a = ((IntV) l).getValue();
                BigInteger b = ((IntV) r).getValue();

                return switch (expr.getOp()) {
                    case ADD -> new IntV(a.add(b));
                    case SUB -> new IntV(a.subtract(b));
                    case MUL -> new IntV(a.multiply(b));
                    case DIV -> {
                        if (b.equals(BigInteger.ZERO)) {
                            throw new RuntimeError("Division by zero");
                        }
                        yield new IntV(a.divide(b));
                    }
                    case MOD -> {
                        if (b.equals(BigInteger.ZERO)) {
                            throw new RuntimeError("Modulo by zero");
                        }
                        yield new IntV(a.mod(b));
                    }

                    case EQ  -> new BoolV(a.equals(b));
                    case NEQ -> new BoolV(!a.equals(b));
                    case LT  -> new BoolV(a.compareTo(b) < 0);
                    case LTE -> new BoolV(a.compareTo(b) <= 0);
                    case GT  -> new BoolV(a.compareTo(b) > 0);
                    case GTE -> new BoolV(a.compareTo(b) >= 0);

                    default -> throw new RuntimeError("Unsupported operator: " + expr.getOp());
                };
            }
        }
    }

    // ---------------- Modality (filtered labels) ----------------

    @Override
    public Value visitModalityExpr(ModalityExpr expr) {
        // labels removed by filter -> runtime no-op
        return expr.getInner().accept(this);
    }

    // ---------------- Type nodes (should never be evaluated) ----------------

    @Override
    public Value visitBuiltinType(BuiltinType expr) {
        throw new RuntimeError("BuiltinType should not be evaluated at runtime");
    }

    @Override
    public Value visitFunctionType(FunctionType type) {
        throw new RuntimeError("FunctionType should not be evaluated at runtime");
    }

    @Override
    public Value visitModalityType(ModalityType type) {
        throw new RuntimeError("ModalityType should not be evaluated at runtime");
    }

    @Override
    public Value visitUnannotatedFunctionType(UnannotatedFunctionType type) {
        throw new RuntimeError("UnannotatedFunctionType should not be evaluated at runtime");
    }
}
