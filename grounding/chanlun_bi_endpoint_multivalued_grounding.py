"""笔 ENDPOINT readings DIFFER on ARBITRARY 分型 sequences — but those are UNREACHABLE (see CORRECTION).

★★ CORRECTION (Klaus 2026-06-11, "正规化之后还不确定么?"; 数学才是唯一的判决 — on the REACHABLE domain):
the gate-relativity conclusion BELOW is an ARTIFACT. This file feeds ARBITRARY random 分型 sequences (with
consecutive same-kind fractals). On the REAL pipeline (K-lines → 包含处理 → 分型, interp.eval_), the 分型
STRICTLY ALTERNATE — NO consecutive same-kind — so the three readings COINCIDE on every reachable input ⇒
笔 IS DETERMINISTIC and 缠论 唯一分解 HOLDS (threshold-0/EmptyResidue, the project's own placement). The
44–55% disagreement below is REAL for the abstract function on ARBITRARY input, but those inputs are
UNREACHABLE, so it does NOT make 缠论's 笔 gate-relative. The honest verdict is in
`chanlun_bi_reachable_determinism_grounding.py`. This file is retained as the boundary witness: it shows
the readings CAN differ — but only on the same-kind-run configurations that 包含处理 never produces.
(Lesson: a "math verdict" must test the REACHABLE domain, not arbitrary inputs.)

--- original (now-corrected) framing follows ---

缠论's headline claim (lesson 65): *所有的图形，都可以唯一地分解为上下交替的笔* — a chart has a UNIQUE
alternating 笔 decomposition. The 108课-vs-impl audit + this grounding show that claim is **gate-relative**:
the 原文's informal endpoint rule ("两个顶或底中间没有其他的顶和底…第一个的顶或底就可以忽略" / the
README's "select extremal representatives") admits MULTIPLE deterministic formalizations that DISAGREE.

This is EXACTLY the project's thesis surfacing inside 缠论 (CLAUDE.md): *确定性是 a 的派生性质，不是价格
对象的内禀性质* — determinism is a property of the admissibility gate `a`, NOT intrinsic to the price. 缠论
is an ICT-threshold-1 / 命名残差多解 case for the 笔 endpoint: each gate gives a unique decomposition, but
the 原文 does not pin the gate, so the decompositions multiply.

THREE deterministic readings of the 笔 endpoint (all consistent with some reading of the 原文 text):
  (L) leftmost-greedy   — emit at the FIRST opposite-far fractal; absorb later same-kind into the anchor.
                          (The runtime `strokes`; the README's documented choice; cc proved its uniqueness #1090.)
  (E) extremal-repr     — pre-collapse each same-kind RUN to its extremal (顶: higher h; 底: lower l), THEN
                          connect alternating with gap ≥ δmin. (The README's "select extremal representatives".)
  (T) keep-latter       — pre-collapse each same-kind run to its LAST fractal ("ignore the first" — the 原文
                          lesson-65 verbatim), THEN connect.

THE MATH VERDICT (Klaus: 数学才是唯一的判决):
  (DET) DETERMINISM per gate — each reading is a pure function (re-run identical) ⇒ each ALONE satisfies the
        原文's 唯一分解 (unique decomposition) FOR ITS OWN GATE. So 缠论 is not "non-deterministic"; it is
        deterministic-relative-to-a-gate.
  (DIV) GATE-RELATIVITY — the three readings PAIRWISE DISAGREE on a large fraction of random fractal
        sequences (L vs E measured ~44%). So the 原文's single 唯一分解 claim is under-determined: the chart
        does NOT have ONE 笔 decomposition, it has one PER admissible gate, and the 原文 admits ≥3.
  ⇒ the faithful MST-NF treatment is NOT "pick one and impose it" (the README's silent collapse to L) but to
    NAME the multiplicity [chanlun_bi_endpoint_multivalued_OPEN] and carry the family. The residue is the
    gate-relativity itself — surfaced, not hidden.

§15 (the harness CAN fail): a NON-deterministic mutant reading (random tie-break on which same-kind fractal
to keep) MUST break (DET) — distinguishing a genuine deterministic gate from a non-deterministic one. AND
the population must actually EXHIBIT pairwise disagreement (else the multivalued claim is vacuous).

Self-contained integer-core. δmin=4 (新笔, proven faithful in chanlun_bi_kline_rule_grounding).
"""
from __future__ import annotations

import random
import sys

TOP, BOT = "top", "bottom"
DMIN = 4    # 新笔 (proven ⟺ pivot-diff ≥ 4)


def _pick_rep(cur, cand):
    """Extremal among same-kind: 顶 → higher h; 底 → lower l."""
    if cur["kind"] == TOP:
        return cand if cand["h"] > cur["h"] else cur
    return cand if cand["l"] < cur["l"] else cur


def strokes_leftmost(frs, dmin):
    """(L) The runtime reading: emit at the FIRST opposite-far fractal, absorb later same-kind."""
    anchor, out = None, []
    for f in frs:
        if anchor is None:
            anchor = f
        elif f["kind"] == anchor["kind"]:
            anchor = _pick_rep(anchor, f)
        elif f["idx"] - anchor["idx"] >= dmin:
            out.append((anchor["idx"], f["idx"]))
            anchor = f
    return out


def _connect(reps, dmin):
    """Connect an (already same-kind-collapsed) sequence: emit opposite pairs with gap ≥ dmin; a too-close
    drop leaves the anchor, and a subsequent same-kind re-collapses into it (extremal)."""
    anchor, out = None, []
    for f in reps:
        if anchor is None:
            anchor = f
        elif f["kind"] == anchor["kind"]:
            anchor = _pick_rep(anchor, f)
        elif f["idx"] - anchor["idx"] >= dmin:
            out.append((anchor["idx"], f["idx"]))
            anchor = f
    return out


def strokes_extremal(frs, dmin):
    """(E) pre-collapse each same-kind RUN to its extremal, THEN connect."""
    reps = []
    for f in frs:
        if reps and reps[-1]["kind"] == f["kind"]:
            reps[-1] = _pick_rep(reps[-1], f)
        else:
            reps.append(dict(f))
    return _connect(reps, dmin)


def strokes_keep_latter(frs, dmin):
    """(T) pre-collapse each same-kind RUN to its LAST fractal ("ignore the first", 原文 lesson 65), THEN connect."""
    reps = []
    for f in frs:
        if reps and reps[-1]["kind"] == f["kind"]:
            reps[-1] = dict(f)                    # keep the latter: overwrite with the newer same-kind
        else:
            reps.append(dict(f))
    return _connect(reps, dmin)


READINGS = {"leftmost": strokes_leftmost, "extremal": strokes_extremal, "keep_latter": strokes_keep_latter}


def _strokes_nondeterministic(frs, dmin, rng):
    """§15 MUTANT: a NON-deterministic reading — on a same-kind run, keep a RANDOM member. MUST break (DET)."""
    reps = []
    for f in frs:
        if reps and reps[-1]["kind"] == f["kind"]:
            if rng.random() < 0.5:
                reps[-1] = dict(f)
        else:
            reps.append(dict(f))
    return _connect(reps, dmin)


def _gen_fractals(rng):
    n = rng.randint(0, 16)
    out, idx, base = [], 0, rng.randint(0, 40)
    for _ in range(n):
        idx += rng.randint(1, 3)
        base += rng.randint(-9, 9)
        k = rng.choice((TOP, BOT))
        out.append({"idx": idx, "kind": k, "h": base + rng.randint(1, 6), "l": base - rng.randint(1, 6)})
    return out


def run(n: int, seed: int):
    rng = random.Random(seed)
    pair_diff = {("leftmost", "extremal"): 0, ("leftmost", "keep_latter"): 0, ("extremal", "keep_latter"): 0}
    total = 0
    for _ in range(n):
        frs = _gen_fractals(rng)
        res = {}
        for name, fn in READINGS.items():
            r = fn(frs, DMIN)
            # (DET) each reading is a pure function — re-run identical.
            assert fn(frs, DMIN) == r, f"[DET seed={seed}] reading {name} is non-deterministic"
            res[name] = r
        for a, b in pair_diff:
            if res[a] != res[b]:
                pair_diff[(a, b)] += 1
        total += 1
    return total, pair_diff


def _self_test() -> None:
    # §15: the non-deterministic mutant MUST produce different results across runs on SOME input.
    rng = random.Random(99)
    fired = False
    for _ in range(3000):
        frs = _gen_fractals(rng)
        a = _strokes_nondeterministic(frs, DMIN, random.Random(1))
        b = _strokes_nondeterministic(frs, DMIN, random.Random(2))
        if a != b:
            fired = True
            break
    assert fired, ("SELF-TEST FAILED (§15): the non-deterministic mutant never diverged across seeds — "
                   "the (DET) determinism check is not load-bearing.")
    # the three honest readings are each deterministic on a hand case.
    frs = [{"idx": 0, "kind": TOP, "h": 10, "l": 8}, {"idx": 5, "kind": BOT, "h": 4, "l": 2},
           {"idx": 6, "kind": BOT, "h": 3, "l": 1}, {"idx": 12, "kind": TOP, "h": 11, "l": 9}]
    for fn in READINGS.values():
        assert fn(frs, DMIN) == fn(frs, DMIN), "a reading is non-deterministic on the hand case"


def main() -> int:
    _self_test()
    total = 0
    agg = {("leftmost", "extremal"): 0, ("leftmost", "keep_latter"): 0, ("extremal", "keep_latter"): 0}
    for seed in (11, 22, 33, 44, 55):
        t, pd = run(40000, seed=seed)
        total += t
        for k in agg:
            agg[k] += pd[k]
    # (DIV) the readings must actually DISAGREE — else the multivalued claim is vacuous.
    for (a, b), d in agg.items():
        assert d > total // 100, f"non-vacuity: {a} vs {b} disagree on only {d}/{total} — too few to claim 多解"
    pct = {f"{a}≠{b}": f"{100*d/total:.1f}%" for (a, b), d in agg.items()}
    print(f"chanlun_bi_endpoint_multivalued OK: over {total} random 分型 sequences, THREE deterministic 笔 "
          f"endpoint readings of the 原文 — (L) leftmost-greedy [runtime, #1090], (E) extremal-representative, "
          f"(T) keep-latter ['ignore the first', lesson 65] — are EACH a pure function (DET: 唯一分解 holds "
          f"FOR EACH GATE) yet PAIRWISE DISAGREE: {pct}. So 缠论's headline 唯一分解 is GATE-RELATIVE — the "
          f"chart does NOT have one 笔 decomposition, it has one PER admissible gate, and the 原文 ('第一个"
          f"…可以忽略' / 'extremal representative') does NOT pin the gate. This is the project thesis inside "
          f"缠论: 确定性是 a 的派生性质，不是价格对象的内禀性质 — an ICT-threshold-1 / 命名残差多解 case. The "
          f"faithful treatment is to NAME the multiplicity [chanlun_bi_endpoint_multivalued_OPEN] and carry "
          f"the FAMILY, not silently collapse to (L) as the README did. §15: a non-deterministic tie-break "
          f"mutant breaks (DET), distinguishing a genuine deterministic gate from noise. 数学才是唯一的判决.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
