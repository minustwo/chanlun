package chanlun

// Def-4 + Lemma 2 stroke greedy, faithful port of
// conformance/chanlun-v1/reference_backend/strokes.py:strokes.
//
// Walk the fractal sequence with a single alternating anchor (leftmost-greedy):
//   - same-kind fractal      -> keep the extremal representative (pick_rep)
//   - opposite-kind & gap>=dmin -> EMIT (anchor->f) and re-anchor to f
//   - opposite-kind but gap<dmin -> drop as named residue
// Dispositions classify EACH fractal as one of {first, absorbed, emit, residue}
// (exhaustion witness; len(dispositions) == len(fractals)).

const (
	DispFirst    = "first"
	DispAbsorbed = "absorbed"
	DispEmit     = "emit"
	DispResidue  = "residue"
)

// Stroke is one emitted line.
type Stroke struct {
	FromIdx int64
	ToIdx   int64
	Dir     string // "up" or "down"
	FromP   int64
	ToP     int64
}

func pickRep(cur, cand Fractal) Fractal {
	if cur.Kind == KindTop {
		if cand.H > cur.H {
			return cand
		}
		return cur
	}
	// bottom -> lower l wins
	if cand.L < cur.L {
		return cand
	}
	return cur
}

// Strokes runs the greedy and returns (strokes, dispositions).
func Strokes(fractals []Fractal, dmin int64) ([]Stroke, []string) {
	var anchor *Fractal
	out := make([]Stroke, 0)
	disp := make([]string, 0, len(fractals))
	for i := range fractals {
		f := fractals[i]
		if anchor == nil {
			a := f
			anchor = &a
			disp = append(disp, DispFirst)
			continue
		}
		if f.Kind == anchor.Kind {
			merged := pickRep(*anchor, f)
			anchor = &merged
			disp = append(disp, DispAbsorbed)
			continue
		}
		// opposite kind
		if f.Idx-anchor.Idx >= dmin {
			var aPrice, fPrice int64
			if anchor.Kind == KindTop {
				aPrice = anchor.H
			} else {
				aPrice = anchor.L
			}
			if f.Kind == KindTop {
				fPrice = f.H
			} else {
				fPrice = f.L
			}
			dir := "down"
			if f.Kind == KindTop {
				dir = "up"
			}
			out = append(out, Stroke{
				FromIdx: anchor.Idx,
				ToIdx:   f.Idx,
				Dir:     dir,
				FromP:   aPrice,
				ToP:     fPrice,
			})
			fc := f
			anchor = &fc
			disp = append(disp, DispEmit)
		} else {
			disp = append(disp, DispResidue)
		}
	}
	return out, disp
}

// StrokesToValue emits a stroke list as a Value tree (objects with the same
// keys as the Python reference; canonical emit re-sorts alphabetically).
func StrokesToValue(ss []Stroke) Value {
	out := make([]Value, len(ss))
	for i, s := range ss {
		o := NewObject()
		o.Set("from_idx", VInt(s.FromIdx))
		o.Set("to_idx", VInt(s.ToIdx))
		o.Set("dir", VStr(s.Dir))
		o.Set("from_p", VInt(s.FromP))
		o.Set("to_p", VInt(s.ToP))
		out[i] = VObj(o)
	}
	return VArr(out)
}

// DispositionsToValue emits ["first","emit",...] as a Value tree.
func DispositionsToValue(disp []string) Value {
	out := make([]Value, len(disp))
	for i, d := range disp {
		out[i] = VStr(d)
	}
	return VArr(out)
}
