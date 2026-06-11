package chanlun

import "fmt"

// RunStage dispatches a single stage by name, mirroring example_phase3_check.py:
// returns the Value tree to be canonicalized.
func RunStage(stage string, inp Value) (Value, error) {
	switch stage {
	case "normalize":
		bars := BarsFromValue(inp)
		out := NormalizeN(bars)
		return BarsToValue(out), nil

	case "fractal":
		bars := BarsFromValue(inp)
		out := ExtractFractals(bars)
		return FractalsToValue(out), nil

	case "stroke":
		o := inp.MustObj()
		fv, _ := o.Get("fractals")
		dv, _ := o.Get("dmin")
		frs := FractalsFromValue(fv)
		dmin := dv.MustInt()
		ss, disp := Strokes(frs, dmin)
		res := NewObject()
		res.Set("strokes", StrokesToValue(ss))
		res.Set("dispositions", DispositionsToValue(disp))
		return VObj(res), nil

	case "zhongshu":
		o := inp.MustObj()
		ev, _ := o.Get("elements")
		zv, _ := o.Get("zone")
		els := ElementsFromValue(ev)
		zone := zv.MustStr()
		cs := Zhongshu(els, zone)
		return CentersToValue(cs), nil

	case "trend_type":
		centers := CentersFromValue(inp)
		return VStr(ClassifyTrend(centers)), nil

	case "pipeline":
		o := inp.MustObj()
		bv, _ := o.Get("bars")
		dv, hasD := o.Get("dmin")
		zv, hasZ := o.Get("zone")
		bars := BarsFromValue(bv)
		dmin := int64(Dmin)
		if hasD {
			dmin = dv.MustInt()
		}
		zone := "first3"
		if hasZ {
			zone = zv.MustStr()
		}
		return RunFull(bars, dmin, zone).ToValue(), nil
	}
	return Value{}, fmt.Errorf("unknown stage: %q", stage)
}
