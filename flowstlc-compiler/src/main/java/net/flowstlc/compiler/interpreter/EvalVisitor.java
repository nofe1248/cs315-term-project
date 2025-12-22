package net.flowstlc.compiler.interpreter;

import net.flowstlc.compiler.ast.*;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class EvalVisitor implements ASTVisitor<Value> {

    private Env env;
    private final String sourceText;

    public EvalVisitor(Env env) {
        this(env, null);
    }

    public EvalVisitor(Env env, String sourceText) {
        this.env = env;
        this.sourceText = sourceText;
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

    @Override
    public Value visitStringLiteralExpr(StringLiteralExpr expr) {
        return new StringV(expr.getValue());
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
            throw new RuntimeError("Condition is not a boolean", expr.getCondition(), sourceText);
        }
        boolean b = ((BoolV) cond).getValue();
        return b
                ? expr.getThenBranch().accept(this)
                : expr.getElseBranch().accept(this);
    }

    @Override
    public Value visitRecordExpr(RecordExpr expr) {
        // Evaluate each field in source order.
        Map<String, Value> evaluated = new LinkedHashMap<>();
        for (Map.Entry<String, Expr> entry : expr.getFields().entrySet()) {
            String field = entry.getKey();
            Value v = entry.getValue().accept(this);
            evaluated.put(field, v);
        }
        return new RecordV(evaluated);
    }

    @Override
    public Value visitRecordFieldAccessExpr(RecordFieldAccessExpr expr) {
        Value recV = expr.getRecordExpr().accept(this);
        if (!(recV instanceof RecordV rv)) {
            throw new RuntimeError("Field access on non-record value", expr, sourceText);
        }

        String field = expr.getFieldName();
        if (!rv.hasField(field)) {
            throw new RuntimeError("Record has no field: " + field, expr, sourceText);
        }
        return rv.getField(field);
    }

    @Override
    public Value visitRecordType(RecordType type) {
        throw new IllegalStateException("EvalVisitor should not evaluate RecordType");
    }


    // ---------------- Function call ----------------

    @Override
    public Value visitFunctionCallExpr(FunctionCallExpr expr) {
        // functionName is a String, lookup from env
        Value fun = env.get(expr.getFunctionName());
        if (!(fun instanceof ClosureV clo)) {
            throw new RuntimeError("Not a function: " + expr.getFunctionName(), expr, sourceText);
        }

        List<String> params = clo.getParams();
        List<Expr> args = expr.getArguments();
        if (params.size() != args.size()) {
            throw new RuntimeError("Argument number mismatch for " + expr.getFunctionName()
                    + ": expected " + params.size() + " got " + args.size(), expr, sourceText);
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
                if (!(v instanceof IntV iv)) {
                    throw new RuntimeError("NEG requires int", expr, sourceText);
                }
                return new IntV(iv.getValue().negate());
            }
            case NOT -> {
                if (!(v instanceof BoolV bv)) {
                    throw new RuntimeError("NOT requires bool", expr, sourceText);
                }
                return new BoolV(!bv.getValue());
            }
            default -> throw new RuntimeError("Unknown unary op: " + expr.getOp(), expr, sourceText);
        }
    }

    @Override
    public Value visitBinaryExpr(BinaryExpr expr) {
        Value l = expr.getLeft().accept(this);
        Value r = expr.getRight().accept(this);

        switch (expr.getOp()) {

            case AND -> {
                if (!(l instanceof BoolV) || !(r instanceof BoolV)) {
                    throw new RuntimeError("AND expects bool", expr, sourceText);
                }
                return new BoolV(((BoolV) l).getValue() && ((BoolV) r).getValue());
            }

            case OR -> {
                if (!(l instanceof BoolV) || !(r instanceof BoolV)) {
                    throw new RuntimeError("OR expects bool", expr, sourceText);
                }
                return new BoolV(((BoolV) l).getValue() || ((BoolV) r).getValue());
            }

            default -> {
                if (!(l instanceof IntV) || !(r instanceof IntV)) {
                    throw new RuntimeError("Binary op expects int", expr, sourceText);
                }

                BigInteger a = ((IntV) l).getValue();
                BigInteger b = ((IntV) r).getValue();

                return switch (expr.getOp()) {
                    case ADD -> new IntV(a.add(b));
                    case SUB -> new IntV(a.subtract(b));
                    case MUL -> new IntV(a.multiply(b));
                    case DIV -> new IntV(a.divide(b));
                    case MOD -> new IntV(a.mod(b));
                    case EQ -> new BoolV(a.equals(b));
                    case NEQ -> new BoolV(!a.equals(b));
                    case LT -> new BoolV(a.compareTo(b) < 0);
                    case LTE -> new BoolV(a.compareTo(b) <= 0);
                    case GT -> new BoolV(a.compareTo(b) > 0);
                    case GTE -> new BoolV(a.compareTo(b) >= 0);
                    default -> throw new RuntimeError("Unknown binary op: " + expr.getOp(), expr, sourceText);
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

    // ---------------- Intrinsic functions ----------------
    /*
      Currently FlowSTLC has the following intrinsic functions:
        - printInt(Int): Int^Pub->Unit and Int^Sec->Unit
        - printBool(Bool): Bool^Pub->Unit and Bool^Sec->Unit
        - printString(String): String^Pub->Unit and String^Sec->Unit
        - readInt(): Unit^Pub->Int
        - readBool(): Unit^Pub->Bool
        - readString(): Unit^Pub->String
        - printf(String, ...): String^Pub, ... -> Unit (the type actually cannot be represented in our type system)
        - format(String, ...): String^Pub, ... -> String (the type actually cannot be represented in our type system)
     */
    @Override
    public Value visitIntrinsicExpr(IntrinsicExpr expr) {
        String name = expr.getIntrinsicName();
        List<Expr> args = expr.getArguments();

        switch (name) {

            case "printInt" -> {
                if (args.size() != 1) {
                    throw new RuntimeError("printInt expects 1 argument", expr, sourceText);
                }
                Value v = args.get(0).accept(this);
                if (!(v instanceof IntV iv)) {
                    throw new RuntimeError("printInt expects an integer", args.get(0), sourceText);
                }
                System.out.println(iv.getValue());
                return UnitV.INSTANCE;
            }

            case "printBool" -> {
                if (args.size() != 1) {
                    throw new RuntimeError("printBool expects 1 argument", expr, sourceText);
                }
                Value v = args.get(0).accept(this);
                if (!(v instanceof BoolV bv)) {
                    throw new RuntimeError("printBool expects a boolean", args.get(0), sourceText);
                }
                System.out.println(bv.getValue());
                return UnitV.INSTANCE;
            }

            case "printString" -> {
                if (args.size() != 1) {
                    throw new RuntimeError("printString expects 1 argument", expr, sourceText);
                }
                Value v = args.get(0).accept(this);
                if (!(v instanceof StringV sv)) {
                    throw new RuntimeError("printString expects a string", args.get(0), sourceText);
                }
                System.out.println(sv.getValue());
                return UnitV.INSTANCE;
            }

            case "readInt" -> {
                if (!args.isEmpty()) {
                    throw new RuntimeError("readInt expects no arguments", expr, sourceText);
                }
                try {
                    byte[] buf = new byte[1024];
                    int n = System.in.read(buf);
                    if (n <= 0) {
                        throw new RuntimeError("Failed to read integer from input", expr, sourceText);
                    }
                    String s = new String(buf, 0, n).trim();
                    return new IntV(new BigInteger(s));
                } catch (RuntimeError re) {
                    throw re;
                } catch (Exception e) {
                    throw new RuntimeError("Failed to read integer from input", expr, sourceText);
                }
            }

            case "readBool" -> {
                if (!args.isEmpty()) {
                    throw new RuntimeError("readBool expects no arguments", expr, sourceText);
                }
                try {
                    byte[] buf = new byte[1024];
                    int n = System.in.read(buf);
                    if (n <= 0) {
                        throw new RuntimeError("Failed to read boolean from input", expr, sourceText);
                    }
                    String s = new String(buf, 0, n).trim();
                    if (s.equalsIgnoreCase("true")) return new BoolV(true);
                    if (s.equalsIgnoreCase("false")) return new BoolV(false);
                    throw new RuntimeError("Failed to read boolean from input", expr, sourceText);
                } catch (RuntimeError re) {
                    throw re;
                } catch (Exception e) {
                    throw new RuntimeError("Failed to read boolean from input", expr, sourceText);
                }
            }

            case "readString" -> {
                if (!args.isEmpty()) {
                    throw new RuntimeError("readString expects no arguments", expr, sourceText);
                }
                try {
                    byte[] buf = new byte[1024];
                    int n = System.in.read(buf);
                    if (n < 0) {
                        throw new RuntimeError("Failed to read string from input", expr, sourceText);
                    }
                    String s = new String(buf, 0, Math.max(0, n));
                    return new StringV(s);
                } catch (RuntimeError re) {
                    throw re;
                } catch (Exception e) {
                    throw new RuntimeError("Failed to read string from input", expr, sourceText);
                }
            }

            case "printf" -> {
                if (args.isEmpty()) {
                    throw new RuntimeError("printf expects at least 1 argument", expr, sourceText);
                }
                Value fmtV = args.get(0).accept(this);
                if (!(fmtV instanceof StringV sv)) {
                    throw new RuntimeError("printf expects first argument to be a string", args.get(0), sourceText);
                }
                String fmt = sv.getValue();
                Object[] fmtArgs = new Object[args.size() - 1];
                for (int i = 1; i < args.size(); i++) {
                    Value v = args.get(i).accept(this);
                    Object ov;
                    if (v instanceof IntV iv) {
                        ov = iv.getValue();
                    } else if (v instanceof BoolV bv) {
                        ov = bv.getValue();
                    } else if (v instanceof StringV ssv) {
                        ov = ssv.getValue();
                    } else if (v instanceof UnitV) {
                        ov = "()";
                    } else {
                        throw new RuntimeError("printf argument has unsupported runtime type", args.get(i), sourceText);
                    }
                    fmtArgs[i - 1] = ov;
                }
                System.out.print(String.format(fmt, fmtArgs));
                return UnitV.INSTANCE;
            }

            case "format" -> {
                if (args.isEmpty()) {
                    throw new RuntimeError("format expects at least 1 argument", expr, sourceText);
                }
                Value fmtV = args.get(0).accept(this);
                if (!(fmtV instanceof StringV sv)) {
                    throw new RuntimeError("format expects first argument to be a string", args.get(0), sourceText);
                }
                String fmt = sv.getValue();
                Object[] fmtArgs = new Object[args.size() - 1];
                for (int i = 1; i < args.size(); i++) {
                    Value v = args.get(i).accept(this);
                    Object ov;
                    if (v instanceof IntV iv) {
                        ov = iv.getValue();
                    } else if (v instanceof BoolV bv) {
                        ov = bv.getValue();
                    } else if (v instanceof StringV ssv) {
                        ov = ssv.getValue();
                    } else if (v instanceof UnitV) {
                        ov = "()";
                    } else {
                        throw new RuntimeError("format argument has unsupported runtime type", args.get(i), sourceText);
                    }
                    fmtArgs[i - 1] = ov;
                }
                return new StringV(String.format(fmt, fmtArgs));
            }

            default -> throw new RuntimeError("Unknown intrinsic: " + name, expr, sourceText);
        }
    }

    @Override
    public Value visitSequenceExpr(SequenceExpr expr) {
        expr.getFirst().accept(this);
        return expr.getSecond().accept(this);
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
