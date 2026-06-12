// Algorithm N (包含处理 / inclusion-normalization) — faithful port of
// conformance/chanlun-v1/reference_backend/normalize.py:normalize_N.
//
// Single-pass left-to-right; append bar; while top two bars are in a CONTAINMENT
// relation (one fully inside the other on [l,h]), replace them with the
// directional merge:
//   up-rule:   {l: max(la,lb), h: max(ha,hb)}
//   down-rule: {l: min(la,lb), h: min(ha,hb)}
// Direction = up iff the new non-contained bar's high exceeds the prior top's
// high (initial direction = up; matches the program's dir=1).

namespace Chanlun;

public static class Normalize
{
    public static List<Bar> NormalizeN(IReadOnlyList<Bar> xs)
    {
        var stack = new List<Bar>(xs.Count);
        bool up = true;
        foreach (var it in xs)
        {
            if (stack.Count == 0)
            {
                stack.Add(it);
                continue;
            }
            var top = stack[^1];
            if (Contained(top, it))
            {
                stack[^1] = Merge(top, it, up);
            }
            else
            {
                stack.Add(it);
                up = it.H > top.H;
            }
        }
        return stack;
    }

    private static bool Contained(Bar a, Bar b)
    {
        bool aInB = b.L <= a.L && a.H <= b.H;
        bool bInA = a.L <= b.L && b.H <= a.H;
        return aInB || bInA;
    }

    private static Bar Merge(Bar a, Bar b, bool up)
    {
        if (up)
            return new Bar(Math.Max(a.L, b.L), Math.Max(a.H, b.H));
        return new Bar(Math.Min(a.L, b.L), Math.Min(a.H, b.H));
    }

    // ---- Value-tree converters ------------------------------------------------

    public static List<Bar> BarsFromValue(Value v)
    {
        var arr = v.AsArray();
        var out_ = new List<Bar>(arr.Count);
        foreach (var e in arr)
        {
            var o = e.AsObject();
            out_.Add(new Bar(o.Get("l").AsInt(), o.Get("h").AsInt()));
        }
        return out_;
    }

    public static Value BarsToValue(IReadOnlyList<Bar> bars)
    {
        var arr = new List<Value>(bars.Count);
        foreach (var b in bars)
        {
            var o = new OrderedObject();
            o.Set("h", Value.Of(b.H));
            o.Set("l", Value.Of(b.L));
            arr.Add(Value.Of(o));
        }
        return Value.Of(arr);
    }
}
