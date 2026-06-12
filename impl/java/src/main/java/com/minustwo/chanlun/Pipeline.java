// Pipeline.java — End-to-end pipeline, faithful port of
// conformance/chanlun-v1/reference_backend/pipeline.py:run_full and the
// stage dispatcher mirroring example_phase3_check.py + impl/go/stage.go.
//
// Stages (left-to-right, deterministic):
//   raw bars -> normalize -> fractals -> strokes -> stroke_elements -> zhongshu -> trend_type
//
// All stages are integer-core, pure functions: same input bytes => same output bytes.
package com.minustwo.chanlun;

import java.util.ArrayList;
import java.util.List;

import com.minustwo.chanlun.Types.Bar;
import com.minustwo.chanlun.Types.Center;
import com.minustwo.chanlun.Types.Element;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Stroke;
import com.minustwo.chanlun.Types.Value;

public final class Pipeline {

    private Pipeline() {}

    /** Default stroke separation gate (xinbi dmin = 4). */
    public static final long DMIN = 4;

    /** Convert strokes to the level-N+1 element shape. */
    public static List<Element> strokesToElements(List<Stroke> ss) {
        List<Element> out = new ArrayList<>(ss.size());
        for (int i = 0; i < ss.size(); i++) {
            Stroke s = ss.get(i);
            long lo = Math.min(s.fromP(), s.toP());
            long hi = Math.max(s.fromP(), s.toP());
            out.add(new Element(i, lo, hi));
        }
        return out;
    }

    /** Result of run_full. */
    public record Result(
        List<Bar> normalizedBars,
        List<Types.Fractal> fractals,
        List<String> strokeDispositions,
        List<Stroke> strokes,
        List<Element> strokeElements,
        String zhongshuZone,
        List<Center> zhongshuCenters,
        String trendType
    ) {}

    public static Result runFull(List<Bar> bars, long dmin, String zone) {
        List<Bar> nb = Normalize.normalizeN(bars);
        List<Types.Fractal> fr = Fractals.extractFractals(nb);
        Strokes.Result sr = Strokes.strokes(fr, dmin);
        List<Element> elems = strokesToElements(sr.strokes());
        List<Center> centers = Zhongshu.zhongshu(elems, zone);
        String trend = TrendType.classify(centers);
        return new Result(nb, fr, sr.dispositions(), sr.strokes(), elems, zone, centers, trend);
    }

    /** Emit the pipeline result as a Value tree, matching the Python reference's run_full dict. */
    public static Value resultToValue(Result p) {
        OrderedObject o = new OrderedObject();
        o.set("normalized_bars", Normalize.barsToValue(p.normalizedBars()));
        o.set("fractals", Fractals.fractalsToValue(p.fractals()));
        o.set("stroke_dispositions", Strokes.dispositionsToValue(p.strokeDispositions()));
        o.set("strokes", Strokes.strokesToValue(p.strokes()));
        o.set("stroke_elements", Zhongshu.elementsToValue(p.strokeElements()));
        o.set("zhongshu_zone", Value.ofString(p.zhongshuZone()));
        o.set("zhongshu_centers", Zhongshu.centersToValue(p.zhongshuCenters()));
        o.set("trend_type", Value.ofString(p.trendType()));
        return Value.ofObject(o);
    }

    /** Stage dispatcher: mirrors example_phase3_check.py + impl/go's RunStage. */
    public static Value runStage(String stage, Value inp) {
        return switch (stage) {
            case "normalize" -> {
                List<Bar> bars = Normalize.barsFromValue(inp);
                yield Normalize.barsToValue(Normalize.normalizeN(bars));
            }
            case "fractal" -> {
                List<Bar> bars = Normalize.barsFromValue(inp);
                yield Fractals.fractalsToValue(Fractals.extractFractals(bars));
            }
            case "stroke" -> {
                OrderedObject o = inp.mustObj();
                List<Types.Fractal> frs = Fractals.fractalsFromValue(o.get("fractals"));
                long dmin = o.get("dmin").mustInt();
                Strokes.Result sr = Strokes.strokes(frs, dmin);
                OrderedObject res = new OrderedObject();
                res.set("strokes", Strokes.strokesToValue(sr.strokes()));
                res.set("dispositions", Strokes.dispositionsToValue(sr.dispositions()));
                yield Value.ofObject(res);
            }
            case "zhongshu" -> {
                OrderedObject o = inp.mustObj();
                List<Element> els = Zhongshu.elementsFromValue(o.get("elements"));
                String zone = o.get("zone").mustStr();
                yield Zhongshu.centersToValue(Zhongshu.zhongshu(els, zone));
            }
            case "trend_type" -> Value.ofString(TrendType.classify(Zhongshu.centersFromValue(inp)));
            case "pipeline" -> {
                OrderedObject o = inp.mustObj();
                List<Bar> bars = Normalize.barsFromValue(o.get("bars"));
                long dmin = o.has("dmin") ? o.get("dmin").mustInt() : DMIN;
                String zone = o.has("zone") ? o.get("zone").mustStr() : "first3";
                yield resultToValue(runFull(bars, dmin, zone));
            }
            default -> throw new IllegalArgumentException("unknown stage: " + stage);
        };
    }
}
