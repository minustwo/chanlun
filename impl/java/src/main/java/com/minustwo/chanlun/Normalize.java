// Normalize.java — Algorithm N (包含处理 / inclusion-normalization, chanlun.pdf
// Appendix A), faithful port of
// conformance/chanlun-v1/reference_backend/normalize.py:normalize_N.
//
// Single-pass left-to-right; for each new bar:
//   - empty stack         -> push
//   - top contains it or  -> directional merge in place (up: max-l max-h;
//     it contains top                                    down: min-l min-h)
//   - non-contained        -> push and update direction (up iff h > prev top's h).
package com.minustwo.chanlun;

import java.util.ArrayList;
import java.util.List;

import com.minustwo.chanlun.Types.Bar;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Value;

public final class Normalize {

    private Normalize() {}

    private static boolean contained(Bar a, Bar b) {
        boolean aInB = b.l() <= a.l() && a.h() <= b.h();
        boolean bInA = a.l() <= b.l() && b.h() <= a.h();
        return aInB || bInA;
    }

    private static Bar merge(Bar a, Bar b, boolean up) {
        if (up) return new Bar(Math.max(a.l(), b.l()), Math.max(a.h(), b.h()));
        return new Bar(Math.min(a.l(), b.l()), Math.min(a.h(), b.h()));
    }

    /** Run the single-pass containment-merge over xs. */
    public static List<Bar> normalizeN(List<Bar> xs) {
        List<Bar> stack = new ArrayList<>(xs.size());
        boolean up = true;
        for (Bar it : xs) {
            if (stack.isEmpty()) {
                stack.add(it);
                continue;
            }
            Bar top = stack.get(stack.size() - 1);
            if (contained(top, it)) {
                stack.set(stack.size() - 1, merge(top, it, up));
            } else {
                stack.add(it);
                up = it.h() > top.h();
            }
        }
        return stack;
    }

    // ==== Value tree adapters ===============================================

    public static List<Bar> barsFromValue(Value v) {
        List<Value> arr = v.mustArr();
        List<Bar> out = new ArrayList<>(arr.size());
        for (Value e : arr) {
            OrderedObject o = e.mustObj();
            out.add(new Bar(o.get("l").mustInt(), o.get("h").mustInt()));
        }
        return out;
    }

    public static Value barsToValue(List<Bar> bars) {
        List<Value> out = new ArrayList<>(bars.size());
        for (Bar b : bars) {
            OrderedObject o = new OrderedObject();
            // Insertion order doesn't matter for the canonical emit (we resort);
            // keep alphabetical for human-readable raw output.
            o.set("h", Value.ofInt(b.h()));
            o.set("l", Value.ofInt(b.l()));
            out.add(Value.ofObject(o));
        }
        return Value.ofArray(out);
    }
}
