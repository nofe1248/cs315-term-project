package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.Program;
import net.flowstlc.compiler.ast.ASTUnannotator;
import net.flowstlc.compiler.interpreter.Interpreter;
import net.flowstlc.compiler.interpreter.RuntimeError;
import net.flowstlc.compiler.interpreter.Value;

import net.flowstlc.compiler.typechecker.TypeChecker;
import net.flowstlc.compiler.typechecker.TypeError;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.IOException;

public class InterpreterMain {
    public static void main(String[] args) throws IOException {
        if (args.length < 1) {
            System.err.println("Usage: <source-file> [entryPoint] [--no-typecheck]");
            System.exit(1);
        }

        String filePath = args[0];
        String entryPoint = "main";
        boolean doTypeCheck = true;

        for (int i = 1; i < args.length; i++) {
            if (args[i].equals("--no-typecheck")) {
                doTypeCheck = false;
            } else {
                entryPoint = args[i];
            }
        }

        CharStream input = CharStreams.fromFileName(filePath);
        FlowSTLCLexer lexer = new FlowSTLCLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FlowSTLCParser parser = new FlowSTLCParser(tokens);

        ParseTree tree = parser.program();

        // ---------- Build full (annotated) AST ----------
        ASTBuilder builder = new ASTBuilder();
        Program fullProgram = builder.build((FlowSTLCParser.ProgramContext) tree);

        // ---------- Optional type check on full AST ----------
        if (doTypeCheck) {
            try {
                TypeChecker tc = new TypeChecker();
                tc.checkProgram(fullProgram, entryPoint);
                System.out.println("[TypeChecker] OK");
            } catch (TypeError e) {
                System.err.println("[TypeChecker] Failed: " + e.getMessage());
                System.exit(1);
            }
        } else {
            System.out.println("[TypeChecker] Skipped (--no-typecheck)");
        }

        // ---------- remove security labels ----------
        ASTUnannotator unannotator = new ASTUnannotator();
        Program unannotated = unannotator.unannotate(fullProgram);

        // ---------- Run interpreter: build global env ----------
        Interpreter interp = new Interpreter();
        interp.run(unannotated);

        // ---------- Call entry point ----------
        Value result = interp.callEntryPoint(entryPoint);

        // ---------- Print final result ----------
        System.out.println(result);

    }
}
