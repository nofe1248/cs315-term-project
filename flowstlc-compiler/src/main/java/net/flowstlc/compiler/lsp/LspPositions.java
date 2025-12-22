package net.flowstlc.compiler.lsp;

import net.flowstlc.compiler.ast.SourceSpan;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;

public final class LspPositions {
    private LspPositions() {}

    public static int offsetAt(String text, Position position) {
        int targetLine = Math.max(0, position.getLine());
        int targetChar = Math.max(0, position.getCharacter());

        int line = 0;
        int i = 0;
        while (i < text.length() && line < targetLine) {
            char ch = text.charAt(i++);
            if (ch == '\n') {
                line++;
            }
        }

        int lineStart = i;
        int lineEnd = lineStart;
        while (lineEnd < text.length() && text.charAt(lineEnd) != '\n') {
            lineEnd++;
        }

        int clampedChar = Math.min(targetChar, lineEnd - lineStart);
        return lineStart + clampedChar;
    }

    public static Position positionAt(String text, int offset) {
        int off = Math.max(0, Math.min(offset, text.length()));

        int line = 0;
        int lineStart = 0;
        for (int i = 0; i < off; i++) {
            if (text.charAt(i) == '\n') {
                line++;
                lineStart = i + 1;
            }
        }
        int ch = off - lineStart;
        return new Position(line, ch);
    }

    public static Range rangeFromSpan(String text, SourceSpan span) {
        if (text == null || span == null || !span.isKnown()) {
            return new Range(new Position(0, 0), new Position(0, 1));
        }
        int start = Math.max(0, Math.min(span.getStartOffset(), text.length()));
        int end = Math.max(start, Math.min(span.getEndOffset(), text.length()));
        Position startPos = positionAt(text, start);
        Position endPos = positionAt(text, end);
        // LSP shouldn't have empty ranges for diagnostics; ensure at least 1 char.
        if (start == end) {
            int bumped = Math.min(text.length(), start + 1);
            endPos = positionAt(text, bumped);
        }
        return new Range(startPos, endPos);
    }

    public static String identifierAt(String text, int offset) {
        if (offset < 0 || offset > text.length()) {
            return null;
        }
        int left = Math.min(offset, text.length() - 1);
        int right = left;

        if (left >= 0 && left < text.length() && !isIdentChar(text.charAt(left))) {
            if (left == 0) {
                return null;
            }
            left--;
            right = left;
        }

        if (left < 0 || left >= text.length() || !isIdentChar(text.charAt(left))) {
            return null;
        }

        while (left > 0 && isIdentChar(text.charAt(left - 1))) {
            left--;
        }
        while (right + 1 < text.length() && isIdentChar(text.charAt(right + 1))) {
            right++;
        }

        String candidate = text.substring(left, right + 1);
        if (candidate.isEmpty()) {
            return null;
        }
        char first = candidate.charAt(0);
        if (!(Character.isLetter(first) || first == '_')) {
            return null;
        }
        return candidate;
    }

    private static boolean isIdentChar(char c) {
        return Character.isLetterOrDigit(c) || c == '_';
    }
}

