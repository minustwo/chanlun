package chanlun

// Algorithm N - inclusion-normalization (chanlun.pdf Appendix A), faithful port
// of conformance/chanlun-v1/reference_backend/normalize.py:normalize_N.
//
// Single-pass left-to-right; append bar; while the top two bars are in a
// CONTAINMENT relation (one fully inside the other on [l,h]), replace them
// with the directional merge:
//   up-rule:   {l: max(la,lb), h: max(ha,hb)}
//   down-rule: {l: min(la,lb), h: min(ha,hb)}
// Direction = up iff the new non-contained bar's high exceeds the prior top's
// high (initial direction = up; matches the program's dir=1).
//
// Bars are objects {l: int, h: int}; we keep them in that representation so
// the canonical emit reproduces the exact Python field order after sort.

// Bar is a price interval (l <= h, but the algorithm itself doesn't enforce).
type Bar struct {
	L int64
	H int64
}

// BarsFromValue parses a list of {l,h} objects.
func BarsFromValue(v Value) []Bar {
	arr := v.MustArr()
	out := make([]Bar, len(arr))
	for i, e := range arr {
		o := e.MustObj()
		l, _ := o.Get("l")
		h, _ := o.Get("h")
		out[i] = Bar{L: l.MustInt(), H: h.MustInt()}
	}
	return out
}

// BarsToValue emits the bar list as a typed Value tree.
func BarsToValue(bars []Bar) Value {
	out := make([]Value, len(bars))
	for i, b := range bars {
		o := NewObject()
		// Insertion order doesn't matter for the canonical emit (we resort), but
		// keep it stable: match the Python reference which emits {"h","l"} after
		// canonical sort -> emit as h then l alphabetically anyway.
		o.Set("h", VInt(b.H))
		o.Set("l", VInt(b.L))
		out[i] = VObj(o)
	}
	return VArr(out)
}

func barContained(a, b Bar) bool {
	aInB := b.L <= a.L && a.H <= b.H
	bInA := a.L <= b.L && b.H <= a.H
	return aInB || bInA
}

func barMerge(a, b Bar, up bool) Bar {
	if up {
		return Bar{L: maxInt(a.L, b.L), H: maxInt(a.H, b.H)}
	}
	return Bar{L: minInt(a.L, b.L), H: minInt(a.H, b.H)}
}

// NormalizeN runs the single-pass containment merge over xs.
func NormalizeN(xs []Bar) []Bar {
	stack := make([]Bar, 0, len(xs))
	up := true
	for _, it := range xs {
		if len(stack) == 0 {
			stack = append(stack, it)
			continue
		}
		top := stack[len(stack)-1]
		if barContained(top, it) {
			stack[len(stack)-1] = barMerge(top, it, up)
		} else {
			stack = append(stack, it)
			up = it.H > top.H
		}
	}
	return stack
}

func maxInt(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
}

func minInt(a, b int64) int64 {
	if a < b {
		return a
	}
	return b
}
