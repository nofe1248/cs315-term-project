# FlowSTLC: An Information Flow Checking Type System Based On Graded Modality And Simply Typed Lambda Calculus
This project proposes the design and implementation of a simple functional programming language with a type system that enforces secure information flow. Building on the simply-typed lambda calculus (STLC), we extend the type system
with a graded modality indexed by two security labels, Secret (confidential) and Public (public). Inspired by [Graded Modal Dependent Type Theory (Moon et al.)](https://dl.acm.org/doi/10.1145/3341714), our system statically prevents unauthorized flows of sensitive data into public outputs, ensuring the noninterference property.

This repository includes:
- A small interpreter for the language written in Java 17 (flowstlc-compiler/)
- A Lean 4 formalization for FlowSTLC (flowstlc/)
- LaTeX source for the final presentation slides (presentation-slides/)
- LaTeX source for the progress report slides (progress-report/)
- LaTeX source & PDF file for the project report (report/)
- A Visual Studio Code extension for FlowSTLC language server (vscode-flowstlc-lsp/)

This is the repository for the term project of the CS315 Computer Security course of Southern University of Science and Technology. For more details please see the [project report](https://github.com/nofe1248/cs315-term-project/blob/main/report/term_project_report.pdf).
