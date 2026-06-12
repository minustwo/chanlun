// Canonical.java — JSON parser + canonical emitter + SHA-256, matching
// Python's
//
//     json.dumps(obj, sort_keys=True, separators=(comma,colon), ensure_ascii=True)
//
// byte-for-byte over the integer/string domain used by the chanlun-v1 corpus.
//
// Why hand-rolled (no Jackson, no Gson)?
//   - Both libs default to insertion-order output AND tolerate floats; getting
//     them to match Python's `sort_keys + ensure_ascii` exactly is more
//     fragile than writing 200 lines of pure-Java emit. Zero runtime deps
//     keeps the jar tiny and the CI step trivial.
//   - Mirrors impl/go/internal/chanlun/canon.go (the Go port made the same
//     call and it's been green on 48/48 for months).
//
// SHA-equality is the law. A byte off = FAIL.
package com.minustwo.chanlun;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HexFormat;
import java.util.List;

import com.minustwo.chanlun.Types.Kind;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Value;

public final class Canonical {

    private Canonical() {}

    // ==== Public API =========================================================

    /** Decode JSON bytes into a typed Value tree. Floats are rejected (corpus
     *  is integer-core). */
    public static Value decode(byte[] bytes) {
        Parser p = new Parser(new String(bytes, StandardCharsets.UTF_8));
        Value v = p.parseValue();
        p.skipWhitespace();
        if (!p.atEnd()) {
            throw new IllegalArgumentException(
                "trailing data after JSON value at offset " + p.pos);
        }
        return v;
    }

    /** Canonical JSON bytes:
     *    - object keys sorted lexicographically (code-point order),
     *    - no whitespace,
     *    - non-ASCII chars escaped as backslash-uXXXX (surrogate pair for >0xFFFF). */
    public static byte[] canonical(Value v) {
        StringBuilder sb = new StringBuilder();
        writeValue(sb, v);
        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }

    /** sha256(bytes) as lowercase hex. */
    public static String sha256Hex(byte[] bytes) {
        try {
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            byte[] digest = md.digest(bytes);
            return HexFormat.of().formatHex(digest);
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 unavailable", e);
        }
    }

    // ==== Canonical emit =====================================================

    private static void writeValue(StringBuilder sb, Value v) {
        switch (v.kind) {
            case NULL -> sb.append("null");
            case BOOL -> sb.append(v.i != 0 ? "true" : "false");
            case INT -> sb.append(Long.toString(v.i));
            case STRING -> writeString(sb, v.s);
            case ARRAY -> {
                sb.append('[');
                boolean first = true;
                for (Value e : v.arr) {
                    if (!first) sb.append(',');
                    first = false;
                    writeValue(sb, e);
                }
                sb.append(']');
            }
            case OBJECT -> {
                sb.append('{');
                List<String> keys = new ArrayList<>(v.obj.keys());
                Collections.sort(keys); // code-point / UTF-16 order; matches Python for ASCII
                boolean first = true;
                for (String k : keys) {
                    if (!first) sb.append(',');
                    first = false;
                    writeString(sb, k);
                    sb.append(':');
                    writeValue(sb, v.obj.get(k));
                }
                sb.append('}');
            }
        }
    }

    /** Emit a JSON string matching Python json.dumps(..., ensure_ascii=True).
     *  Escapes: quote, backslash, b, f, n, r, t; backslash-u00xx for control bytes < 0x20; raw ASCII
     *  for 0x20..0x7e; backslash-uXXXX for >= 0x7f (surrogate pair for code points
     *  beyond the BMP). */
    private static void writeString(StringBuilder sb, String s) {
        sb.append('"');
        int len = s.length();
        for (int i = 0; i < len; ) {
            int cp = s.codePointAt(i);
            i += Character.charCount(cp);
            switch (cp) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\b' -> sb.append("\\b");
                case '\f' -> sb.append("\\f");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> {
                    if (cp < 0x20) {
                        sb.append(String.format("\\u%04x", cp));
                    } else if (cp < 0x7f) {
                        sb.append((char) cp);
                    } else if (cp <= 0xFFFF) {
                        sb.append(String.format("\\u%04x", cp));
                    } else {
                        // Encode as UTF-16 surrogate pair to match Python's
                        // json.dumps(..., ensure_ascii=True) behavior.
                        int u = cp - 0x10000;
                        int high = 0xD800 | ((u >>> 10) & 0x3FF);
                        int low  = 0xDC00 | (u & 0x3FF);
                        sb.append(String.format("\\u%04x\\u%04x", high, low));
                    }
                }
            }
        }
        sb.append('"');
    }

    // ==== Parser =============================================================

    private static final class Parser {
        final String src;
        int pos;

        Parser(String s) { this.src = s; this.pos = 0; }

        boolean atEnd() { return pos >= src.length(); }

        void skipWhitespace() {
            while (pos < src.length()) {
                char c = src.charAt(pos);
                if (c == ' ' || c == '\n' || c == '\r' || c == '\t') {
                    pos++;
                } else {
                    return;
                }
            }
        }

        Value parseValue() {
            skipWhitespace();
            if (pos >= src.length()) throw new IllegalArgumentException("unexpected end of input");
            char c = src.charAt(pos);
            return switch (c) {
                case '{' -> parseObject();
                case '[' -> parseArray();
                case '"' -> Value.ofString(parseString());
                case 't', 'f' -> parseBool();
                case 'n' -> parseNull();
                default -> parseNumber();
            };
        }

        Value parseObject() {
            expect('{');
            OrderedObject o = new OrderedObject();
            skipWhitespace();
            if (peek() == '}') { pos++; return Value.ofObject(o); }
            while (true) {
                skipWhitespace();
                String k = parseString();
                skipWhitespace();
                expect(':');
                Value v = parseValue();
                o.set(k, v);
                skipWhitespace();
                char c = peek();
                if (c == ',') { pos++; continue; }
                if (c == '}') { pos++; return Value.ofObject(o); }
                throw new IllegalArgumentException("expected , or } at " + pos + " got " + c);
            }
        }

        Value parseArray() {
            expect('[');
            List<Value> out = new ArrayList<>();
            skipWhitespace();
            if (peek() == ']') { pos++; return Value.ofArray(out); }
            while (true) {
                out.add(parseValue());
                skipWhitespace();
                char c = peek();
                if (c == ',') { pos++; continue; }
                if (c == ']') { pos++; return Value.ofArray(out); }
                throw new IllegalArgumentException("expected , or ] at " + pos + " got " + c);
            }
        }

        String parseString() {
            expect('"');
            StringBuilder sb = new StringBuilder();
            while (pos < src.length()) {
                char c = src.charAt(pos++);
                if (c == '"') return sb.toString();
                if (c == '\\') {
                    if (pos >= src.length()) throw new IllegalArgumentException("trailing backslash");
                    char esc = src.charAt(pos++);
                    switch (esc) {
                        case '"' -> sb.append('"');
                        case '\\' -> sb.append('\\');
                        case '/' -> sb.append('/');
                        case 'b' -> sb.append('\b');
                        case 'f' -> sb.append('\f');
                        case 'n' -> sb.append('\n');
                        case 'r' -> sb.append('\r');
                        case 't' -> sb.append('\t');
                        case 'u' -> {
                            if (pos + 4 > src.length()) {
                                throw new IllegalArgumentException("short \\u escape");
                            }
                            int hex = Integer.parseInt(src.substring(pos, pos + 4), 16);
                            pos += 4;
                            // Surrogate pair: handle if hex is high surrogate and next is backslash-uXXXX low.
                            if (hex >= 0xD800 && hex <= 0xDBFF
                                && pos + 6 <= src.length()
                                && src.charAt(pos) == '\\'
                                && src.charAt(pos + 1) == 'u') {
                                int low = Integer.parseInt(src.substring(pos + 2, pos + 6), 16);
                                pos += 6;
                                if (low >= 0xDC00 && low <= 0xDFFF) {
                                    int cp = 0x10000 + ((hex - 0xD800) << 10) + (low - 0xDC00);
                                    sb.appendCodePoint(cp);
                                    continue;
                                }
                                // Not a valid low surrogate — fall back to emitting the high as-is.
                                sb.append((char) hex);
                                sb.append((char) low);
                            } else {
                                sb.append((char) hex);
                            }
                        }
                        default -> throw new IllegalArgumentException("bad escape \\" + esc);
                    }
                } else {
                    sb.append(c);
                }
            }
            throw new IllegalArgumentException("unterminated string");
        }

        Value parseBool() {
            if (src.startsWith("true", pos)) { pos += 4; return Value.ofBool(true); }
            if (src.startsWith("false", pos)) { pos += 5; return Value.ofBool(false); }
            throw new IllegalArgumentException("expected bool at " + pos);
        }

        Value parseNull() {
            if (src.startsWith("null", pos)) { pos += 4; return Value.ofNull(); }
            throw new IllegalArgumentException("expected null at " + pos);
        }

        Value parseNumber() {
            int start = pos;
            if (peek() == '-') pos++;
            while (pos < src.length() && Character.isDigit(src.charAt(pos))) pos++;
            // Reject floats: chanlun-v1 corpus is integer-core; a `.`, `e`, or
            // `E` here would mean someone shipped a non-conformant fixture
            // (or a backend leaked a float). Surface as an error.
            if (pos < src.length()) {
                char c = src.charAt(pos);
                if (c == '.' || c == 'e' || c == 'E') {
                    throw new IllegalArgumentException(
                        "chanlun-v1 is integer-core; refusing non-integer number at " + start);
                }
            }
            String num = src.substring(start, pos);
            if (num.isEmpty() || num.equals("-")) {
                throw new IllegalArgumentException("expected number at " + start);
            }
            return Value.ofInt(Long.parseLong(num));
        }

        void expect(char c) {
            if (pos >= src.length() || src.charAt(pos) != c) {
                throw new IllegalArgumentException("expected '" + c + "' at " + pos);
            }
            pos++;
        }

        char peek() {
            if (pos >= src.length()) throw new IllegalArgumentException("unexpected end of input");
            return src.charAt(pos);
        }
    }

    // Convenience: read a file as bytes (used from harness only; here so the
    // tests stay free of java.nio noise).
    public static byte[] readAllBytes(java.nio.file.Path p) {
        try {
            return java.nio.file.Files.readAllBytes(p);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
