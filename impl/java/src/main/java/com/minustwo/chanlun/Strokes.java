// Strokes.java — Def-4 + Lemma 2 stroke greedy, faithful port of
// conformance/chanlun-v1/reference_backend/strokes.py:strokes.
//
// Walk the fractal sequence with a single alternating anchor (leftmost-greedy):
//   - same-kind fractal           -> keep the extremal rep (pickRep)
//   - opposite-kind, gap >= dmin  -> EMIT (anchor->f) and re-anchor to f
//   - opposite-kind, gap <  dmin  -> drop as named residue
// dispositions[i] classifies fractal i as one of {first, absorbed, emit, residue}.
package com.minustwo.chanlun;

import java.util.ArrayList;
import java.util.List;

import com.minustwo.chanlun.Types.Fractal;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Stroke;
import com.minustwo.chanlun.Types.Value;

public final class Strokes {

    private Strokes() {}

    /** Extremal representative among same-kind fractals: top -> higher h; bottom -> lower l. */
    private static Fractal pickRep(Fractal cur, Fractal cand) {
        if (Types.FRACTAL_TOP.equals(cur.kind())) {
            return cand.h() > cur.h() ? cand : cur;
        }
        return cand.l() < cur.l() ? cand : cur;
    }

    /** Result holder for the (strokes, dispositions) tuple. */
    public record Result(List<Stroke> strokes, List<String> dispositions) {}

    /** Run the greedy. Returns (strokes, dispositions). */
    public static Result strokes(List<Fractal> fractals, long dmin) {
        Fractal anchor = null;
        List<Stroke> out = new ArrayList<>();
        List<String> disp = new ArrayList<>(fractals.size());
        for (Fractal f : fractals) {
            if (anchor == null) {
                anchor = f;
                disp.add(Types.DISP_FIRST);
                continue;
            }
            if (f.kind().equals(anchor.kind())) {
                anchor = pickRep(anchor, f);
                disp.add(Types.DISP_ABSORBED);
                continue;
            }
            // opposite kind
            if (f.idx() - anchor.idx() >= dmin) {
                long aPrice = Types.FRACTAL_TOP.equals(anchor.kind()) ? anchor.h() : anchor.l();
                long fPrice = Types.FRACTAL_TOP.equals(f.kind()) ? f.h() : f.l();
                String dir = Types.FRACTAL_TOP.equals(f.kind()) ? "up" : "down";
                out.add(new Stroke(anchor.idx(), f.idx(), dir, aPrice, fPrice));
                anchor = f;
                disp.add(Types.DISP_EMIT);
            } else {
                disp.add(Types.DISP_RESIDUE);
            }
        }
        return new Result(out, disp);
    }

    // ==== Value tree adapters ===============================================

    public static Value strokesToValue(List<Stroke> ss) {
        List<Value> out = new ArrayList<>(ss.size());
        for (Stroke s : ss) {
            OrderedObject o = new OrderedObject();
            o.set("from_idx", Value.ofInt(s.fromIdx()));
            o.set("to_idx", Value.ofInt(s.toIdx()));
            o.set("dir", Value.ofString(s.dir()));
            o.set("from_p", Value.ofInt(s.fromP()));
            o.set("to_p", Value.ofInt(s.toP()));
            out.add(Value.ofObject(o));
        }
        return Value.ofArray(out);
    }

    public static Value dispositionsToValue(List<String> disp) {
        List<Value> out = new ArrayList<>(disp.size());
        for (String d : disp) out.add(Value.ofString(d));
        return Value.ofArray(out);
    }
}
