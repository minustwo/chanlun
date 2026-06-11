package chanlun

// End-to-end pipeline, faithful port of
// conformance/chanlun-v1/reference_backend/pipeline.py:run_full.

// Dmin is the default stroke separation gate (xinbi dmin = 4).
const Dmin = 4

// PipelineResult is the canonical decomposition dict shape every Phase-3
// implementation must reproduce byte-for-byte.
type PipelineResult struct {
	NormalizedBars     []Bar
	Fractals           []Fractal
	StrokeDispositions []string
	Strokes            []Stroke
	StrokeElements     []Element
	ZhongshuZone       string
	ZhongshuCenters    []Center
	TrendType          string
}

// StrokesToElements converts strokes to the level-N+1 element shape.
func StrokesToElements(ss []Stroke) []Element {
	out := make([]Element, len(ss))
	for i, s := range ss {
		lo := s.FromP
		hi := s.ToP
		if hi < lo {
			lo, hi = hi, lo
		}
		out[i] = Element{Idx: int64(i), Lo: lo, Hi: hi}
	}
	return out
}

// RunFull drives the full pipeline end-to-end.
func RunFull(bars []Bar, dmin int64, zone string) PipelineResult {
	nb := NormalizeN(bars)
	fr := ExtractFractals(nb)
	st, disp := Strokes(fr, dmin)
	elems := StrokesToElements(st)
	centers := Zhongshu(elems, zone)
	trend := ClassifyTrend(centers)
	return PipelineResult{
		NormalizedBars:     nb,
		Fractals:           fr,
		StrokeDispositions: disp,
		Strokes:            st,
		StrokeElements:     elems,
		ZhongshuZone:       zone,
		ZhongshuCenters:    centers,
		TrendType:          trend,
	}
}

// ToValue emits the pipeline result as a Value tree matching the Python
// reference's run_full dict shape.
func (p PipelineResult) ToValue() Value {
	o := NewObject()
	o.Set("normalized_bars", BarsToValue(p.NormalizedBars))
	o.Set("fractals", FractalsToValue(p.Fractals))
	o.Set("stroke_dispositions", DispositionsToValue(p.StrokeDispositions))
	o.Set("strokes", StrokesToValue(p.Strokes))
	o.Set("stroke_elements", ElementsToValue(p.StrokeElements))
	o.Set("zhongshu_zone", VStr(p.ZhongshuZone))
	o.Set("zhongshu_centers", CentersToValue(p.ZhongshuCenters))
	o.Set("trend_type", VStr(p.TrendType))
	return VObj(o)
}
