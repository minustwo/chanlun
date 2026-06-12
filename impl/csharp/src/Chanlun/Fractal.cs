// Def-3 fractal classifier — faithful port of
// conformance/chanlun-v1/reference_backend/fractal.py.
//
//   Top at i:    H_i > H_{i-1} && H_i > H_{i+1} && L_i > L_{i-1} && L_i > L_{i+1}
//   Bottom at i: L_i < L_{i-1} && L_i < L_{i+1} && H_i < H_{i-1} && H_i < H_{i+1}
// Neither = named structural residue (dropped; gaps in idx).

namespace Chanlun;

public static class FractalOps
{
    public static List<Fractal> ExtractFractals(IReadOnlyList<Bar> bars)
    {
        var out_ = new List<Fractal>();
        int n = bars.Count;
        for (int i = 1; i < n - 1; i++)
        {
            var a = bars[i - 1];
            var b = bars[i];
            var c = bars[i + 1];
            if (IsTop(a, b, c))
                out_.Add(new Fractal(i, Kinds.Top, b.H, b.L));
            else if (IsBottom(a, b, c))
                out_.Add(new Fractal(i, Kinds.Bottom, b.H, b.L));
            // neither -> dropped
        }
        return out_;
    }

    private static bool IsTop(Bar a, Bar b, Bar c)
        => b.H > a.H && b.H > c.H && b.L > a.L && b.L > c.L;

    private static bool IsBottom(Bar a, Bar b, Bar c)
        => b.L < a.L && b.L < c.L && b.H < a.H && b.H < c.H;

    // ---- Value-tree converters ------------------------------------------------

    public static List<Fractal> FractalsFromValue(Value v)
    {
        var arr = v.AsArray();
        var out_ = new List<Fractal>(arr.Count);
        foreach (var e in arr)
        {
            var o = e.AsObject();
            out_.Add(new Fractal(
                o.Get("idx").AsInt(),
                o.Get("kind").AsString(),
                o.Get("h").AsInt(),
                o.Get("l").AsInt()));
        }
        return out_;
    }

    public static Value FractalsToValue(IReadOnlyList<Fractal> fs)
    {
        var arr = new List<Value>(fs.Count);
        foreach (var f in fs)
        {
            var o = new OrderedObject();
            o.Set("idx", Value.Of(f.Idx));
            o.Set("kind", Value.Of(f.Kind));
            o.Set("h", Value.Of(f.H));
            o.Set("l", Value.Of(f.L));
            arr.Add(Value.Of(o));
        }
        return Value.Of(arr);
    }
}
