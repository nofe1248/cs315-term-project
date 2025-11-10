package net.flowstlc.compiler;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import net.flowstlc.compiler.ast.ASTPrinter;

public class Main {
    public static void main(String[] args) {
        try {
            CharStream input = CharStreams.fromFileName(args[0]);
            FlowSTLCLexer lexer = new FlowSTLCLexer(input);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            FlowSTLCParser parser = new FlowSTLCParser(tokens);
            FlowSTLCParser.ProgramContext tree = parser.program();

            ASTBuilder builder = new ASTBuilder();
            var program = builder.build(tree);

            ASTPrinter printer = new ASTPrinter();
            printer.print(program);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
