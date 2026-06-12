// 走势中枢 decomposition — faithful port of
// conformance/chanlun-v1/reference_backend/zhongshu.py:zhongshu.
//
// Scan a list of elements (each {idx, lo, hi}); a center forms iff
// max(lo of first 3) <= min(hi of first 3) (ZD <= ZG). Extend with subsequent
// elements overlapping [zd, zg]. Zone gate:
//   "first3" - test zone stays fixed at the first-3 overlap;
//   "all"    - re-tighten zd/zg to the running overlap of all members.
// On no-overlap: slide one element. Output is the list of
// {start, end, ZD, ZG, n} per center.

namespace Chanlun;

public static class ZhongshuOps
{
    public static List<Center> Zhongshu(IReadOnlyList<Element> els, string zone)
    {
        var centers = new List<Center>();
        int n = els.Count;
        int i = 0;
        while (i + 2 < n)
        {
            long ZD = Math.Max(Math.Max(els[i].Lo, els[i + 1].Lo), els[i + 2].Lo);
            long ZG = Math.Min(Math.Min(els[i].Hi, els[i + 1].Hi), els[i + 2].Hi);
            if (ZD <= ZG)
            {
                var members = new List<int> { i, i + 1, i + 2 };
                long zd = ZD, zg = ZG;
                int j = i + 3;
                while (j < n && els[j].Lo <= zg && els[j].Hi >= zd)
                {
                    members.Add(j);
                    if (zone == "all")
                    {
                        zd = Math.Max(zd, els[j].Lo);
                        zg = Math.Min(zg, els[j].Hi);
                    }
                    j++;
                }
                int last = members[^1];
                centers.Add(new Center(i, last, ZD, ZG, members.Count));
                i = last + 1;
            }
            else
            {
                i++;
            }
        }
        return centers;
    }

    // ---- Value-tree converters ------------------------------------------------

    public static List<Element> ElementsFromValue(Value v)
    {
        var arr = v.AsArray();
        var out_ = new List<Element>(arr.Count);
        foreach (var e in arr)
        {
            var o = e.AsObject();
            out_.Add(new Element(
                o.Get("idx").AsInt(),
                o.Get("lo").AsInt(),
                o.Get("hi").AsInt()));
        }
        return out_;
    }

    public static Value ElementsToValue(IReadOnlyList<Element> els)
    {
        var arr = new List<Value>(els.Count);
        foreach (var el in els)
        {
            var o = new OrderedObject();
            o.Set("idx", Value.Of(el.Idx));
            o.Set("lo", Value.Of(el.Lo));
            o.Set("hi", Value.Of(el.Hi));
            arr.Add(Value.Of(o));
        }
        return Value.Of(arr);
    }

    public static Value CentersToValue(IReadOnlyList<Center> cs)
    {
        var arr = new List<Value>(cs.Count);
        foreach (var c in cs)
        {
            var o = new OrderedObject();
            o.Set("start", Value.Of(c.Start));
            o.Set("end", Value.Of(c.End));
            o.Set("ZD", Value.Of(c.ZD));
            o.Set("ZG", Value.Of(c.ZG));
            o.Set("n", Value.Of(c.N));
            arr.Add(Value.Of(o));
        }
        return Value.Of(arr);
    }

    /// <summary>
    /// Parse a list of centers (trend_type input). The fixtures may or may not
    /// carry start/end/n; defaults to 0 (the trend classifier only reads ZD/ZG).
    /// </summary>
    public static List<Center> CentersFromValue(Value v)
    {
        var arr = v.AsArray();
        var out_ = new List<Center>(arr.Count);
        foreach (var e in arr)
        {
            var o = e.AsObject();
            long start = o.TryGet("start", out var s) ? s.AsInt() : 0;
            long end = o.TryGet("end", out var en) ? en.AsInt() : 0;
            long n = o.TryGet("n", out var nv) ? nv.AsInt() : 0;
            out_.Add(new Center(
                start, end,
                o.Get("ZD").AsInt(),
                o.Get("ZG").AsInt(),
                n));
        }
        return out_;
    }
}
