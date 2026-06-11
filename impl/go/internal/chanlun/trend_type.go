package chanlun

// Trend-type classifier (走势类型), faithful port of
// conformance/chanlun-v1/reference_backend/trend_type.py:classify.
//
//   0 centers           -> "none"
//   1 center            -> "consolidation"
//   >=2 all stepping up -> "trend_up"
//   >=2 all stepping dn -> "trend_down"
//   otherwise           -> "mixed"  (named residue, never silent)
//
// Step direction prev->cur is +1 if cur.ZD > prev.ZG, -1 if cur.ZG < prev.ZD,
// 0 otherwise (overlap / no clean step).

const (
	TrendConsolidation = "consolidation"
	TrendUp            = "trend_up"
	TrendDown          = "trend_down"
	TrendMixed         = "mixed"
	TrendNone          = "none"
)

func stepDir(prev, cur Center) int {
	if cur.ZD > prev.ZG {
		return +1
	}
	if cur.ZG < prev.ZD {
		return -1
	}
	return 0
}

// ClassifyTrend returns the trend-type string.
func ClassifyTrend(centers []Center) string {
	n := len(centers)
	if n == 0 {
		return TrendNone
	}
	if n == 1 {
		return TrendConsolidation
	}
	allUp, allDown := true, true
	for k := 0; k < n-1; k++ {
		d := stepDir(centers[k], centers[k+1])
		if d != +1 {
			allUp = false
		}
		if d != -1 {
			allDown = false
		}
	}
	if allUp {
		return TrendUp
	}
	if allDown {
		return TrendDown
	}
	return TrendMixed
}
