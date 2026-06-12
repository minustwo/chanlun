// Def-4 + Lemma 2 stroke greedy — faithful port of
// conformance/chanlun-v1/reference_backend/strokes.py:strokes.
//
// Walk the fractal sequence with a single alternating anchor (leftmost-greedy):
//   - same-kind fractal      -> keep extremal rep (pick_rep)
//   - opposite-kind & gap>=dmin -> EMIT (anchor->f) and re-anchor to f
//   - opposite-kind but gap<dmin -> drop as named residue
// Dispositions classify EACH fractal into one of
// {first, absorbed, emit, residue} (exhaustion witness).

namespace Chanlun;

public static class StrokeOps
{
    public static (List<Stroke> strokes, List<string> dispositions) Strokes(
        IReadOnlyList<Fractal> fractals, long dmin)
    {
        var outStrokes = new List<Stroke>();
        var disp = new List<string>(fractals.Count);
        bool hasAnchor = false;
        Fractal anchor = default;
        foreach (var f in fractals)
        {
            if (!hasAnchor)
            {
                anchor = f;
                hasAnchor = true;
                disp.Add(Dispositions.First);
                continue;
            }
            if (f.Kind == anchor.Kind)
            {
                anchor = PickRep(anchor, f);
                disp.Add(Dispositions.Absorbed);
                continue;
            }
            // opposite kind
            if (f.Idx - anchor.Idx >= dmin)
            {
                long aPrice = anchor.Kind == Kinds.Top ? anchor.H : anchor.L;
                long fPrice = f.Kind == Kinds.Top ? f.H : f.L;
                string dir = f.Kind == Kinds.Top ? "up" : "down";
                outStrokes.Add(new Stroke(anchor.Idx, f.Idx, dir, aPrice, fPrice));
                anchor = f;
                disp.Add(Dispositions.Emit);
            }
            else
            {
                disp.Add(Dispositions.Residue);
            }
        }
        return (outStrokes, disp);
    }

    private static Fractal PickRep(Fractal cur, Fractal cand)
    {
        if (cur.Kind == Kinds.Top)
            return cand.H > cur.H ? cand : cur;
        // bottom: lower l wins
        return cand.L < cur.L ? cand : cur;
    }

    // ---- Value-tree converters ------------------------------------------------

    public static Value StrokesToValue(IReadOnlyList<Stroke> ss)
    {
        var arr = new List<Value>(ss.Count);
        foreach (var s in ss)
        {
            var o = new OrderedObject();
            // Insertion order doesn't matter (canonical re-sorts) — match
            // Python field order anyway for readability.
            o.Set("from_idx", Value.Of(s.FromIdx));
            o.Set("to_idx", Value.Of(s.ToIdx));
            o.Set("dir", Value.Of(s.Dir));
            o.Set("from_p", Value.Of(s.FromP));
            o.Set("to_p", Value.Of(s.ToP));
            arr.Add(Value.Of(o));
        }
        return Value.Of(arr);
    }

    public static Value DispositionsToValue(IReadOnlyList<string> disp)
    {
        var arr = new List<Value>(disp.Count);
        foreach (var d in disp)
            arr.Add(Value.Of(d));
        return Value.Of(arr);
    }
}
