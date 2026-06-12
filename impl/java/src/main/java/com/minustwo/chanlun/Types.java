// Types.java — typed JSON value tree + insertion-ordered object map + record types
// for Bar / Fractal / Stroke / Element / Center, faithful to the Python reference
// shapes (conformance/chanlun-v1/reference_backend/).
//
// Integer-core: the chanlun-v1 corpus carries NO floats anywhere; we keep a
// strict INT-vs-other distinction so the canonical emit cannot silently
// downconvert a stray float into an int.
package com.minustwo.chanlun;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class Types {

    private Types() {}

    // ==== Value tree =========================================================

    public enum Kind { NULL, BOOL, INT, STRING, ARRAY, OBJECT }

    /** Typed JSON value. We deliberately do NOT support floats — the corpus is
     *  integer-core and decoding refuses non-integer numbers (matches the Go
     *  port's behavior: any float in input is an error, not a silent convert). */
    public static final class Value {
        public final Kind kind;
        public final long i;            // int payload (also bool: 0/1)
        public final String s;          // string payload
        public final List<Value> arr;   // array payload
        public final OrderedObject obj; // object payload

        private Value(Kind k, long i, String s, List<Value> arr, OrderedObject obj) {
            this.kind = k;
            this.i = i;
            this.s = s;
            this.arr = arr;
            this.obj = obj;
        }

        public static Value ofNull() { return new Value(Kind.NULL, 0, null, null, null); }
        public static Value ofBool(boolean b) { return new Value(Kind.BOOL, b ? 1 : 0, null, null, null); }
        public static Value ofInt(long n) { return new Value(Kind.INT, n, null, null, null); }
        public static Value ofString(String s) { return new Value(Kind.STRING, 0, s, null, null); }
        public static Value ofArray(List<Value> a) { return new Value(Kind.ARRAY, 0, null, a, null); }
        public static Value ofObject(OrderedObject o) { return new Value(Kind.OBJECT, 0, null, null, o); }

        public OrderedObject mustObj() {
            if (kind != Kind.OBJECT) throw new IllegalStateException("mustObj: kind=" + kind);
            return obj;
        }
        public List<Value> mustArr() {
            if (kind != Kind.ARRAY) throw new IllegalStateException("mustArr: kind=" + kind);
            return arr;
        }
        public long mustInt() {
            if (kind != Kind.INT) throw new IllegalStateException("mustInt: kind=" + kind);
            return i;
        }
        public String mustStr() {
            if (kind != Kind.STRING) throw new IllegalStateException("mustStr: kind=" + kind);
            return s;
        }
    }

    /** Insertion-ordered string→Value map. The canonical emitter re-sorts keys
     *  lexicographically (UTF-8 byte order — matches Python's
     *  json.dumps(sort_keys=True) for ASCII keys, which is all the corpus uses). */
    public static final class OrderedObject {
        private final LinkedHashMap<String, Value> data = new LinkedHashMap<>();

        public OrderedObject set(String key, Value v) {
            data.put(key, v);
            return this;
        }
        public Value get(String key) { return data.get(key); }
        public boolean has(String key) { return data.containsKey(key); }
        public int size() { return data.size(); }
        public Iterable<Map.Entry<String, Value>> entries() { return data.entrySet(); }
        public List<String> keys() { return new ArrayList<>(data.keySet()); }
    }

    // ==== Domain records =====================================================

    /** Bar — integer price interval {l, h} (l <= h, but the algorithm itself
     *  does not enforce that). */
    public record Bar(long l, long h) {}

    /** Fractal — emitted top or bottom at index `idx` in the normalized bars. */
    public record Fractal(long idx, String kind, long h, long l) {}
    public static final String FRACTAL_TOP = "top";
    public static final String FRACTAL_BOTTOM = "bottom";

    /** Stroke — one emitted line in the 笔 greedy. */
    public record Stroke(long fromIdx, long toIdx, String dir, long fromP, long toP) {}
    public static final String DISP_FIRST = "first";
    public static final String DISP_ABSORBED = "absorbed";
    public static final String DISP_EMIT = "emit";
    public static final String DISP_RESIDUE = "residue";

    /** Element — input shape for zhongshu (one stroke or segment {idx, lo, hi}). */
    public record Element(long idx, long lo, long hi) {}

    /** Center — one emitted 中枢 (走势中枢). */
    public record Center(long start, long end, long ZD, long ZG, long n) {}

    public static final String TREND_CONSOLIDATION = "consolidation";
    public static final String TREND_UP = "trend_up";
    public static final String TREND_DOWN = "trend_down";
    public static final String TREND_MIXED = "mixed";
    public static final String TREND_NONE = "none";
}
