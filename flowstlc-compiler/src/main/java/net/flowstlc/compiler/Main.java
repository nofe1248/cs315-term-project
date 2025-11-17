package net.flowstlc.compiler;

import static net.sourceforge.argparse4j.impl.Arguments.storeTrue;
import net.sourceforge.argparse4j.ArgumentParsers;
import net.sourceforge.argparse4j.inf.ArgumentParser;
import net.sourceforge.argparse4j.inf.Namespace;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import net.flowstlc.compiler.ast.ASTPrinter;

public class Main {
    public static void main(String[] args) {
        ArgumentParser argumentParser = ArgumentParsers.newFor("flowstlc-compiler").build()
                .defaultHelp(true)
                .description("FlowSTLC Interpreter");
        argumentParser.addArgument("--source")
                .help("Path to the FlowSTLC source file")
                .metavar("SOURCE")
                .type(String.class)
                .required(true);
        argumentParser.addArgument("--entry-point")
                .help("Entry point function name")
                .metavar("ENTRY_POINT")
                .type(String.class)
                .setDefault("main");
        argumentParser.addArgument("--dump-ast")
                .help("Dump AST")
                .action(storeTrue());
        argumentParser.addArgument("--debug")
                .help("Enable debug mode")
                .action(storeTrue());
        argumentParser.addArgument("--dump-unannotated-ast")
                .help("Dump unannotated AST")
                .action(storeTrue());
        try {
            Namespace ns = argumentParser.parseArgs(args);
            CharStream input = CharStreams.fromFileName(ns.getString("source"));
            FlowSTLCLexer lexer = new FlowSTLCLexer(input);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            FlowSTLCParser parser = new FlowSTLCParser(tokens);
            FlowSTLCParser.ProgramContext tree = parser.program();

            ASTBuilder builder = new ASTBuilder();
            var program = builder.build(tree);

            if (ns.getBoolean("dump_ast")) {
                ASTPrinter printer = new ASTPrinter();
                printer.print(program);
            }
        } catch (Exception e) {
            System.err.println("Error while running flowstlc-compiler: " + e.getMessage());
            e.printStackTrace(System.err);
        }
    }
}
