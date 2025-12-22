package net.flowstlc.compiler.ast;

import java.util.Objects;

public final class SourceSpan {
    public static final SourceSpan UNKNOWN = new SourceSpan(-1, -1);

    private final int startOffset;
    private final int endOffset;

    public SourceSpan(int startOffset, int endOffset) {
        this.startOffset = startOffset;
        this.endOffset = endOffset;
    }

    public int getStartOffset() {
        return startOffset;
    }

    public int getEndOffset() {
        return endOffset;
    }

    public boolean isKnown() {
        return startOffset >= 0 && endOffset >= 0 && endOffset >= startOffset;
    }

    public int length() {
        return isKnown() ? (endOffset - startOffset) : 0;
    }

    @Override
    public String toString() {
        return isKnown() ? ("[" + startOffset + "," + endOffset + ")") : "<unknown>";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof SourceSpan that)) return false;
        return startOffset == that.startOffset && endOffset == that.endOffset;
    }

    @Override
    public int hashCode() {
        return Objects.hash(startOffset, endOffset);
    }
}

