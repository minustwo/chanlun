package chanlun

// Zhongshu (走势中枢) decomposition, faithful port of
// conformance/chanlun-v1/reference_backend/zhongshu.py:zhongshu.
//
// Scan a list of elements (each {idx, lo, hi}); a center forms iff
// max(lo of first 3) <= min(hi of first 3) (ZD <= ZG). Extend with subsequent
// elements that still overlap [zd, zg]. Zone gate:
//   "first3" - the test zone stays fixed at the first-3 overlap;
//   "all"    - re-tighten zd/zg to the running overlap of all members.
// On no-overlap, slide one element. Output is the list of
// {start, end, ZD, ZG, n} per center.

// Element is one input price-range (a stroke or segment in element form).
type Element struct {
	Idx int64
	Lo  int64
	Hi  int64
}

// Center is one emitted zhongshu.
type Center struct {
	Start int64
	End   int64
	ZD    int64
	ZG    int64
	N     int64
}

// ElementsFromValue parses a list of {idx, lo, hi}.
func ElementsFromValue(v Value) []Element {
	arr := v.MustArr()
	out := make([]Element, len(arr))
	for i, e := range arr {
		o := e.MustObj()
		idx, _ := o.Get("idx")
		lo, _ := o.Get("lo")
		hi, _ := o.Get("hi")
		out[i] = Element{Idx: idx.MustInt(), Lo: lo.MustInt(), Hi: hi.MustInt()}
	}
	return out
}

// ElementsToValue emits an element list as a Value tree.
func ElementsToValue(els []Element) Value {
	out := make([]Value, len(els))
	for i, el := range els {
		o := NewObject()
		o.Set("idx", VInt(el.Idx))
		o.Set("lo", VInt(el.Lo))
		o.Set("hi", VInt(el.Hi))
		out[i] = VObj(o)
	}
	return VArr(out)
}

// Zhongshu runs the decomposition with the named zone gate.
func Zhongshu(els []Element, zone string) []Center {
	centers := make([]Center, 0)
	n := len(els)
	i := 0
	for i+2 < n {
		ZD := maxInt(maxInt(els[i].Lo, els[i+1].Lo), els[i+2].Lo)
		ZG := minInt(minInt(els[i].Hi, els[i+1].Hi), els[i+2].Hi)
		if ZD <= ZG {
			members := []int{i, i + 1, i + 2}
			zd, zg := ZD, ZG
			j := i + 3
			for j < n && els[j].Lo <= zg && els[j].Hi >= zd {
				members = append(members, j)
				if zone == "all" {
					zd = maxInt(zd, els[j].Lo)
					zg = minInt(zg, els[j].Hi)
				}
				j++
			}
			last := members[len(members)-1]
			centers = append(centers, Center{
				Start: int64(i),
				End:   int64(last),
				ZD:    ZD,
				ZG:    ZG,
				N:     int64(len(members)),
			})
			i = last + 1
		} else {
			i++
		}
	}
	return centers
}

// CentersToValue emits a center list as a Value tree.
func CentersToValue(cs []Center) Value {
	out := make([]Value, len(cs))
	for i, c := range cs {
		o := NewObject()
		o.Set("start", VInt(c.Start))
		o.Set("end", VInt(c.End))
		o.Set("ZD", VInt(c.ZD))
		o.Set("ZG", VInt(c.ZG))
		o.Set("n", VInt(c.N))
		out[i] = VObj(o)
	}
	return VArr(out)
}

// CentersFromValue parses a list of {ZD, ZG, end, n, start} (trend_type input).
func CentersFromValue(v Value) []Center {
	arr := v.MustArr()
	out := make([]Center, len(arr))
	for i, e := range arr {
		o := e.MustObj()
		zd, _ := o.Get("ZD")
		zg, _ := o.Get("ZG")
		// trend_type fixtures may or may not carry start/end/n; default to 0.
		var start, end, n int64
		if v, ok := o.Get("start"); ok {
			start = v.MustInt()
		}
		if v, ok := o.Get("end"); ok {
			end = v.MustInt()
		}
		if v, ok := o.Get("n"); ok {
			n = v.MustInt()
		}
		out[i] = Center{Start: start, End: end, ZD: zd.MustInt(), ZG: zg.MustInt(), N: n}
	}
	return out
}
