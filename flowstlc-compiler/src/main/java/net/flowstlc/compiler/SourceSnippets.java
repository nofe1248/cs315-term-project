package net.flowstlc.compiler;

import net.flowstlc.compiler.ast.SourceSpan;

public final class SourceSnippets {
    private SourceSnippets() {}

    public static String snippet(String source, SourceSpan span) {
        if (source == null || span == null || !span.isKnown()) {
            return "";
        }

        int start = clamp(span.getStartOffset(), 0, source.length());
        int end = clamp(span.getEndOffset(), 0, source.length());
        if (end < start) {
            end = start;
        }

        int caretEnd = Math.max(end, Math.min(start + 1, source.length()));

        int lineStart = start;
        while (lineStart > 0 && source.charAt(lineStart - 1) != '\n') {
            lineStart--;
        }

        int lineEnd = start;
        while (lineEnd < source.length() && source.charAt(lineEnd) != '\n') {
            lineEnd++;
        }

        String line = source.substring(lineStart, lineEnd);

        int colStart = start - lineStart;
        int colEnd = Math.min(caretEnd, lineEnd) - lineStart;
        colStart = clamp(colStart, 0, line.length());
        colEnd = clamp(colEnd, colStart, line.length());

        StringBuilder sb = new StringBuilder();
        sb.append(line);
        sb.append('\n');
        sb.append(" ".repeat(colStart));
        sb.append("^".repeat(Math.max(1, colEnd - colStart)));

        if (end > lineEnd) {
            sb.append(" …");
        }

        return sb.toString();
    }

    public static String excerpt(String source, SourceSpan span) {
        if (source == null || span == null || !span.isKnown()) {
            return "";
        }
        int start = clamp(span.getStartOffset(), 0, source.length());
        int end = clamp(span.getEndOffset(), 0, source.length());
        if (end < start) {
            end = start;
        }
        return source.substring(start, end);
    }

    private static int clamp(int v, int lo, int hi) {
        return Math.max(lo, Math.min(hi, v));
    }
}

