"""STANDALONE 缠论 Definition 3 — 分型 (Fractal) classifier on a normalized bar sequence.

This is the pure-stdlib operator-side classifier matching
`lean/Chanlun/Fractal.lean` (`classifyDef3`) — Definition 3 of `chanlun.md`:

    Top fractal at i:     H_i > H_{i-1} ∧ H_i > H_{i+1} ∧ L_i > L_{i-1} ∧ L_i > L_{i+1}
    Bottom fractal at i:  L_i < L_{i-1} ∧ L_i < L_{i+1} ∧ H_i < H_{i-1} ∧ H_i < H_{i+1}
    (Lemma 1: every interior position is exactly one of top / bottom / neither.)

The `[chanlun_inclusion_precondition]` precondition: this Def-3 predicate ASSUMES the
input bar sequence is already 包含处理 normalized (`normalize.normalize_N`). The runner
upstream stage feeds normalized bars in.

Output: a list of fractals {idx, kind ∈ {"top","bottom"}, h, l}. NON-fractal interior
positions become the NAMED structural residue `neither` and are dropped from the output —
their presence is reflected by gaps in `idx`.

Self-contained (pure stdlib).
"""
from __future__ import annotations

TOP = "top"
BOTTOM = "bottom"
NEITHER = "neither"


def _is_top(a, b, c) -> bool:
    """Def-3 top: middle (b) strictly above both neighbours on H AND on L."""
    return (b["h"] > a["h"]) and (b["h"] > c["h"]) and (b["l"] > a["l"]) and (b["l"] > c["l"])


def _is_bottom(a, b, c) -> bool:
    """Def-3 bottom: middle (b) strictly below both neighbours on H AND on L."""
    return (b["l"] < a["l"]) and (b["l"] < c["l"]) and (b["h"] < a["h"]) and (b["h"] < c["h"])


def classify_window(a, b, c) -> str:
    """Def-3 classification on a single 3-bar window. Returns 'top', 'bottom', or 'neither'."""
    if _is_top(a, b, c):
        return TOP
    if _is_bottom(a, b, c):
        return BOTTOM
    return NEITHER


def extract_fractals(bars):
    """Extract the fractal sequence from a normalized bar list (assumed `noAdjBarContainment`).

    Returns a list of fractals: {idx, kind, h, l} with idx = position in `bars` (the
    middle bar of the window). Boundary bars (idx 0, idx len-1) are not classified —
    Def-3 requires a 3-bar window, so they're NEITHER by construction.
    """
    n = len(bars)
    out = []
    for i in range(1, n - 1):
        kind = classify_window(bars[i - 1], bars[i], bars[i + 1])
        if kind == NEITHER:
            continue
        out.append({"idx": i, "kind": kind, "h": bars[i]["h"], "l": bars[i]["l"]})
    return out
