package chanlun

// Def-3 (Fractal) classifier, faithful port of
// conformance/chanlun-v1/reference_backend/fractal.py.
//
// Top at i:    H_i > H_{i-1} && H_i > H_{i+1} && L_i > L_{i-1} && L_i > L_{i+1}
// Bottom at i: L_i < L_{i-1} && L_i < L_{i+1} && H_i < H_{i-1} && H_i < H_{i+1}
// Neither is the named structural residue and is dropped (gaps in idx).

const (
	KindTop    = "top"
	KindBottom = "bottom"
)

// Fractal is an emitted (top or bottom) fractal at position idx in the bar list.
type Fractal struct {
	Idx  int64
	Kind string
	H    int64
	L    int64
}

func isTop(a, b, c Bar) bool {
	return b.H > a.H && b.H > c.H && b.L > a.L && b.L > c.L
}

func isBottom(a, b, c Bar) bool {
	return b.L < a.L && b.L < c.L && b.H < a.H && b.H < c.H
}

// ExtractFractals scans an already-normalized bar list and emits the
// {idx, kind, h, l} sequence (interior windows only).
func ExtractFractals(bars []Bar) []Fractal {
	n := len(bars)
	out := make([]Fractal, 0)
	for i := 1; i < n-1; i++ {
		a, b, c := bars[i-1], bars[i], bars[i+1]
		switch {
		case isTop(a, b, c):
			out = append(out, Fractal{Idx: int64(i), Kind: KindTop, H: b.H, L: b.L})
		case isBottom(a, b, c):
			out = append(out, Fractal{Idx: int64(i), Kind: KindBottom, H: b.H, L: b.L})
		default:
			// 'neither' - dropped (named residue, gap in idx)
		}
	}
	return out
}

// FractalsFromValue parses a JSON list of fractals.
func FractalsFromValue(v Value) []Fractal {
	arr := v.MustArr()
	out := make([]Fractal, len(arr))
	for i, e := range arr {
		o := e.MustObj()
		idx, _ := o.Get("idx")
		kind, _ := o.Get("kind")
		h, _ := o.Get("h")
		l, _ := o.Get("l")
		out[i] = Fractal{
			Idx:  idx.MustInt(),
			Kind: kind.MustStr(),
			H:    h.MustInt(),
			L:    l.MustInt(),
		}
	}
	return out
}

// FractalsToValue emits the fractal list as a typed Value tree.
func FractalsToValue(fs []Fractal) Value {
	out := make([]Value, len(fs))
	for i, f := range fs {
		o := NewObject()
		o.Set("idx", VInt(f.Idx))
		o.Set("kind", VStr(f.Kind))
		o.Set("h", VInt(f.H))
		o.Set("l", VInt(f.L))
		out[i] = VObj(o)
	}
	return VArr(out)
}
