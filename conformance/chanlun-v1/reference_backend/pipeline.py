"""End-to-end Chanlun pipeline assembled from the standalone stage oracles.

Stages (left-to-right, deterministic):

    raw_bars         (list of {l, h} integer bars)
        --[normalize.normalize_N]-->        normalized_bars   (no-adjacent-containment)
        --[fractal.extract_fractals]-->     fractals          (Def-3 top/bottom, alternating on
                                                              reachable / normalized input)
        --[strokes.strokes(dmin=4)]-->      strokes           (Def-4 + Lemma 2, alternating, >= dmin)
        --[strokes -> element form]-->      stroke_elements   ({idx, lo, hi} per stroke)
        --[zhongshu.zhongshu(zone)]-->      zhongshu_centers  (>=3-overlap, per zone gate)
        --[trend_type.classify]-->          trend_type        in {consolidation, trend_up, trend_down,
                                                                  mixed, none}

All stages are integer-core (no floats). All stages are deterministic pure functions: the same
input bytes produce the same output bytes. The corpus FREEZES that contract.
"""
from __future__ import annotations

from . import normalize as _normalize
from . import fractal as _fractal
from . import strokes as _strokes
from . import zhongshu as _zhongshu
from . import trend_type as _trend_type


# Default stroke separation (xinbi dmin = 4, proven faithful in
# `chanlun_bi_kline_rule_grounding.py`).
DMIN = 4


def normalize(bars):
    """Algorithm N - single-pass inclusion-normalization (Appendix A). Returns the normalized stack."""
    return _normalize.normalize_N(bars)


def fractals(normalized_bars):
    """Def-3 fractal extraction over a normalized bar list."""
    return _fractal.extract_fractals(normalized_bars)


def strokes(fractal_list, dmin: int = DMIN):
    """Def-4 + Lemma 2 stroke greedy. Returns (strokes_list, dispositions)."""
    return _strokes.strokes(fractal_list, dmin)


def strokes_to_elements(stroke_list):
    """Convert strokes ({from_idx, to_idx, from_p, to_p, dir}) into zhongshu elements
    ({idx, lo, hi}) suitable as the level-N+1 input."""
    out = []
    for i, s in enumerate(stroke_list):
        lo = min(s["from_p"], s["to_p"])
        hi = max(s["from_p"], s["to_p"])
        out.append({"idx": i, "lo": lo, "hi": hi})
    return out


def zhongshu(elements, zone: str = "first3"):
    """Center decomposition. `zone` in {first3, all}. Returns the list of centers."""
    return _zhongshu.zhongshu(elements, zone)


def classify(centers) -> str:
    """Trend type (lesson 17). Returns one of consolidation / trend_up / trend_down / mixed / none."""
    return _trend_type.classify(centers)


def run_full(bars, dmin: int = DMIN, zone: str = "first3"):
    """Drive the full pipeline end-to-end. Returns the canonical decomposition dict - exactly the
    shape every Phase-3 multi-language implementation MUST reproduce byte-for-byte."""
    nb = normalize(bars)
    fr = fractals(nb)
    st, disp = strokes(fr, dmin)
    elems = strokes_to_elements(st)
    centers = zhongshu(elems, zone)
    trend = classify(centers)
    return {
        "normalized_bars": nb,
        "fractals": fr,
        "stroke_dispositions": disp,
        "strokes": st,
        "stroke_elements": elems,
        "zhongshu_zone": zone,
        "zhongshu_centers": centers,
        "trend_type": trend,
    }
