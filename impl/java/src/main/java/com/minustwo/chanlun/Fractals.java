// Fractals.java — Def-3 (分型) classifier, faithful port of
// conformance/chanlun-v1/reference_backend/fractal.py.
//
// Top at i:    H_i > H_{i-1} && H_i > H_{i+1} && L_i > L_{i-1} && L_i > L_{i+1}
// Bottom at i: L_i < L_{i-1} && L_i < L_{i+1} && H_i < H_{i-1} && H_i < H_{i+1}
// Boundary positions (i = 0, i = n-1) are NEITHER by construction; NEITHER
// fractals are dropped (gaps in idx).
package com.minustwo.chanlun;

import java.util.ArrayList;
import java.util.List;

import com.minustwo.chanlun.Types.Bar;
import com.minustwo.chanlun.Types.Fractal;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Value;

public final class Fractals {

    private Fractals() {}

    private static boolean isTop(Bar a, Bar b, Bar c) {
        return b.h() > a.h() && b.h() > c.h() && b.l() > a.l() && b.l() > c.l();
    }

    private static boolean isBottom(Bar a, Bar b, Bar c) {
        return b.l() < a.l() && b.l() < c.l() && b.h() < a.h() && b.h() < c.h();
    }

    /** Scan a normalized bar list and emit the {idx, kind, h, l} sequence. */
    public static List<Fractal> extractFractals(List<Bar> bars) {
        int n = bars.size();
        List<Fractal> out = new ArrayList<>();
        for (int i = 1; i < n - 1; i++) {
            Bar a = bars.get(i - 1);
            Bar b = bars.get(i);
            Bar c = bars.get(i + 1);
            if (isTop(a, b, c)) {
                out.add(new Fractal(i, Types.FRACTAL_TOP, b.h(), b.l()));
            } else if (isBottom(a, b, c)) {
                out.add(new Fractal(i, Types.FRACTAL_BOTTOM, b.h(), b.l()));
            }
            // else NEITHER -> dropped (named residue, gap in idx)
        }
        return out;
    }

    // ==== Value tree adapters ===============================================

    public static List<Fractal> fractalsFromValue(Value v) {
        List<Value> arr = v.mustArr();
        List<Fractal> out = new ArrayList<>(arr.size());
        for (Value e : arr) {
            OrderedObject o = e.mustObj();
            out.add(new Fractal(
                o.get("idx").mustInt(),
                o.get("kind").mustStr(),
                o.get("h").mustInt(),
                o.get("l").mustInt()));
        }
        return out;
    }

    public static Value fractalsToValue(List<Fractal> fs) {
        List<Value> out = new ArrayList<>(fs.size());
        for (Fractal f : fs) {
            OrderedObject o = new OrderedObject();
            o.set("idx", Value.ofInt(f.idx()));
            o.set("kind", Value.ofString(f.kind()));
            o.set("h", Value.ofInt(f.h()));
            o.set("l", Value.ofInt(f.l()));
            out.add(Value.ofObject(o));
        }
        return Value.ofArray(out);
    }
}
