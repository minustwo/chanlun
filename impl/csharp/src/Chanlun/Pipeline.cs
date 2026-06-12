// End-to-end Chanlun pipeline — faithful port of
// conformance/chanlun-v1/reference_backend/pipeline.py:run_full.

namespace Chanlun;

public static class Pipeline
{
    /// <summary>Default stroke separation (xinbi dmin = 4).</summary>
    public const long Dmin = 4;

    public static List<Element> StrokesToElements(IReadOnlyList<Stroke> strokes)
    {
        var out_ = new List<Element>(strokes.Count);
        for (int i = 0; i < strokes.Count; i++)
        {
            var s = strokes[i];
            long lo = Math.Min(s.FromP, s.ToP);
            long hi = Math.Max(s.FromP, s.ToP);
            out_.Add(new Element(i, lo, hi));
        }
        return out_;
    }

    public static PipelineResult RunFull(IReadOnlyList<Bar> bars, long dmin, string zone)
    {
        var nb = Normalize.NormalizeN(bars);
        var fr = FractalOps.ExtractFractals(nb);
        var (st, disp) = StrokeOps.Strokes(fr, dmin);
        var elems = StrokesToElements(st);
        var centers = ZhongshuOps.Zhongshu(elems, zone);
        var trend = TrendTypeOps.Classify(centers);
        return new PipelineResult(nb, fr, disp, st, elems, zone, centers, trend);
    }

    public static Value ToValue(PipelineResult p)
    {
        var o = new OrderedObject();
        o.Set("normalized_bars", Normalize.BarsToValue(p.NormalizedBars));
        o.Set("fractals", FractalOps.FractalsToValue(p.Fractals));
        o.Set("stroke_dispositions", StrokeOps.DispositionsToValue(p.StrokeDispositions));
        o.Set("strokes", StrokeOps.StrokesToValue(p.Strokes));
        o.Set("stroke_elements", ZhongshuOps.ElementsToValue(p.StrokeElements));
        o.Set("zhongshu_zone", Value.Of(p.ZhongshuZone));
        o.Set("zhongshu_centers", ZhongshuOps.CentersToValue(p.ZhongshuCenters));
        o.Set("trend_type", Value.Of(p.TrendType));
        return Value.Of(o);
    }

    /// <summary>
    /// Dispatch a single stage by name. Mirrors runner.py:run_stage and
    /// impl/go's stage.go.
    /// </summary>
    public static Value RunStage(string stage, Value input)
    {
        switch (stage)
        {
            case "normalize":
                {
                    var bars = Normalize.BarsFromValue(input);
                    var nb = Normalize.NormalizeN(bars);
                    return Normalize.BarsToValue(nb);
                }
            case "fractal":
                {
                    var bars = Normalize.BarsFromValue(input);
                    var fr = FractalOps.ExtractFractals(bars);
                    return FractalOps.FractalsToValue(fr);
                }
            case "stroke":
                {
                    var o = input.AsObject();
                    var frs = FractalOps.FractalsFromValue(o.Get("fractals"));
                    var dmin = o.Get("dmin").AsInt();
                    var (ss, disp) = StrokeOps.Strokes(frs, dmin);
                    var res = new OrderedObject();
                    res.Set("strokes", StrokeOps.StrokesToValue(ss));
                    res.Set("dispositions", StrokeOps.DispositionsToValue(disp));
                    return Value.Of(res);
                }
            case "zhongshu":
                {
                    var o = input.AsObject();
                    var els = ZhongshuOps.ElementsFromValue(o.Get("elements"));
                    var zone = o.Get("zone").AsString();
                    var cs = ZhongshuOps.Zhongshu(els, zone);
                    return ZhongshuOps.CentersToValue(cs);
                }
            case "trend_type":
                {
                    var centers = ZhongshuOps.CentersFromValue(input);
                    return Value.Of(TrendTypeOps.Classify(centers));
                }
            case "pipeline":
                {
                    var o = input.AsObject();
                    var bars = Normalize.BarsFromValue(o.Get("bars"));
                    long dmin = o.TryGet("dmin", out var dv) ? dv.AsInt() : Dmin;
                    string zone = o.TryGet("zone", out var zv) ? zv.AsString() : "first3";
                    return ToValue(RunFull(bars, dmin, zone));
                }
            default:
                throw new InvalidOperationException($"unknown stage: {stage}");
        }
    }
}
