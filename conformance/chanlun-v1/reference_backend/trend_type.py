"""走势类型 (盘整 / 趋势, lesson 17) — classify a 走势 by its 中枢 count + direction, math-first.

The 缠论 走势 axiom (lesson 17): *任何级别的所有走势，都能分解成趋势与盘整两类* — every 走势 is exactly
ONE of 趋势 (trend) or 盘整 (consolidation). The criterion is purely a 中枢 count + directionality:
  盘整 (consolidation): the completed 走势 contains EXACTLY ONE 中枢.
      *某完成的走势类型只包含一个缠中说禅走势中枢，就称为…盘整* (lesson 17, verbatim)
  趋势 (trend): the completed 走势 contains TWO OR MORE 依次同向 (sequentially same-direction) 中枢.
      *至少包含两个以上依次同向的缠中说禅走势中枢，就称为…趋势* (lesson 17, verbatim)
  上涨趋势 = the 中枢s step UP (each later 中枢 entirely above the previous: ZD_next > ZG_prev);
  下跌趋势 = step DOWN (ZG_next < ZD_prev). 依次同向 (the load-bearing qualifier) = ALL consecutive
  中枢 pairs step the SAME direction.

This consumes the 中枢 decomposition (from chanlun_zhongshu). The classification function itself, GIVEN the
中枢s, is a pure function — deterministic. CORRECTION-AWARE (Klaus 2026-06-11, #1096): the levels BELOW are
NOT gate-relative on the reachable domain — after 包含处理, 分型 strictly alternate, so 笔 and 中枢 are
DETERMINISTIC (chanlun_bi_reachable_determinism_grounding). So 走势类型 inherits DETERMINISM, not multi-
valuedness, all the way down. 确定性是 a 的派生性质 (a derived property of the normalize gate a, CLAUDE.md)
— and a IS pinned on the reachable domain, so the whole tower is single-valued; threshold-0 / EmptyResidue.

THE MATH VERDICT (Klaus: 数学才是唯一的判决), over random 中枢 sequences (each an integer zone [ZD,ZG]):
  (TOTAL/EXCLUSIVE) classify ∈ {consolidation, trend_up, trend_down, none} is TOTAL and the 趋势/盘整
        split is the 缠论 axiom made decidable: 1 中枢 ⇒ 盘整; ≥2 依次同向 ⇒ 趋势; ≥2 NOT-all-same-direction
        ⇒ NAMED residue `mixed` (the 走势 is not a clean single type at this level — it needs a 级别 lift or
        is a larger 盘整). NEVER a silent default — every 中枢-count/direction lands in exactly one class.
  (DET) the classifier is a PURE function (re-run identical) — 走势类型 唯一 per gate.
  (DIR) a 趋势 is monotone: trend_up ⇒ every consecutive 中枢 pair steps up; trend_down ⇒ steps down. The
        '依次同向' qualifier is enforced (NOT merely "≥2 中枢").

§15 (the harness CAN fail): a MUTANT classifier that calls ANY ≥2 中枢 a 趋势 (dropping 依次同向) MUST
disagree with the honest classifier on a 中枢 sequence whose centers do NOT all step the same way — proving
the directionality qualifier is load-bearing (a non-monotone ≥2-中枢 走势 is `mixed`, not a 趋势). Non-vacuity:
the population must contain 盘整, both 趋势 directions, AND mixed cases.

HONEST SCOPE: this is the per-走势 CLASSIFICATION given its 中枢s. The DECOMPOSITION of a price stream into
maximal 走势 (and the 级别 lift where a completed 走势 becomes one 次级别 unit of the higher level) are the
named follow-ups [chanlun_walk_decomposition_OPEN] / [chanlun_level_recursion_OPEN]. Integer-core.
"""
from __future__ import annotations

import random
import sys

CONSOLIDATION, TREND_UP, TREND_DOWN, MIXED, NONE = (
    "consolidation", "trend_up", "trend_down", "mixed", "none")


def _step_dir(prev, cur):
    """Direction of stepping from 中枢 prev=[ZD,ZG] to cur: +1 up (cur entirely above), -1 down
    (cur entirely below), 0 overlapping/none (not a clean directional step)."""
    if cur["ZD"] > prev["ZG"]:
        return +1
    if cur["ZG"] < prev["ZD"]:
        return -1
    return 0


def classify(centers) -> str:
    """走势类型 of a completed 走势 with the given 中枢 list. Total + never-silent."""
    n = len(centers)
    if n == 0:
        return NONE                                   # no 中枢 — not a classifiable completed 走势
    if n == 1:
        return CONSOLIDATION                          # exactly one 中枢 ⇒ 盘整 (lesson 17)
    dirs = [_step_dir(centers[k], centers[k + 1]) for k in range(n - 1)]
    if all(d == +1 for d in dirs):
        return TREND_UP                               # ≥2 中枢, all stepping up ⇒ 上涨趋势
    if all(d == -1 for d in dirs):
        return TREND_DOWN                             # all stepping down ⇒ 下跌趋势
    return MIXED                                      # ≥2 中枢 but NOT 依次同向 ⇒ named residue


def _classify_mutant(centers) -> str:
    """§15 MUTANT: any ≥2 中枢 is a '趋势' (drops 依次同向). MUST disagree with `classify` on a mixed case."""
    n = len(centers)
    if n == 0:
        return NONE
    if n == 1:
        return CONSOLIDATION
    return TREND_UP                                   # BUG: calls every ≥2-中枢 走势 a trend


def _gen_centers(rng):
    """A random 中枢 sequence (each an integer zone [ZD,ZG], ZD≤ZG), drifting so that 盘整, both 趋势
    directions, and mixed cases all occur."""
    n = rng.randint(0, 5)
    out, base = [], rng.randint(0, 100)
    for _ in range(n):
        base += rng.randint(-20, 20)                  # may step up, down, or overlap → all classes occur
        half = rng.randint(1, 8)
        zd, zg = base - half, base + half
        out.append({"ZD": zd, "ZG": zg})
    return out


def run(n: int, seed: int):
    rng = random.Random(seed)
    hist = {CONSOLIDATION: 0, TREND_UP: 0, TREND_DOWN: 0, MIXED: 0, NONE: 0}
    for _ in range(n):
        centers = _gen_centers(rng)
        cls = classify(centers)
        # (TOTAL) every input lands in exactly one named class — never None-as-silent.
        assert cls in hist, f"[TOTAL seed={seed}] classify returned unnamed {cls!r}"
        # (DET) pure function.
        assert classify(centers) == cls, f"[DET seed={seed}] classify non-deterministic"
        # (DIR) a trend is genuinely monotone.
        if cls == TREND_UP:
            assert all(_step_dir(centers[k], centers[k + 1]) == +1 for k in range(len(centers) - 1)), \
                f"[DIR seed={seed}] trend_up not all-up: {centers}"
        if cls == TREND_DOWN:
            assert all(_step_dir(centers[k], centers[k + 1]) == -1 for k in range(len(centers) - 1)), \
                f"[DIR seed={seed}] trend_down not all-down: {centers}"
        hist[cls] += 1
    return hist


def _self_test() -> None:
    # hand cases.
    assert classify([]) == NONE
    assert classify([{"ZD": 10, "ZG": 20}]) == CONSOLIDATION
    assert classify([{"ZD": 0, "ZG": 5}, {"ZD": 10, "ZG": 15}]) == TREND_UP        # steps up
    assert classify([{"ZD": 10, "ZG": 15}, {"ZD": 0, "ZG": 5}]) == TREND_DOWN      # steps down
    assert classify([{"ZD": 0, "ZG": 5}, {"ZD": 10, "ZG": 15}, {"ZD": 8, "ZG": 12}]) == MIXED  # up then overlap
    # §15: the mutant (any ≥2 = trend) MUST disagree with classify on a MIXED case.
    mixed = [{"ZD": 0, "ZG": 5}, {"ZD": 10, "ZG": 15}, {"ZD": 8, "ZG": 12}]
    assert classify(mixed) == MIXED and _classify_mutant(mixed) == TREND_UP and \
        classify(mixed) != _classify_mutant(mixed), \
        "SELF-TEST FAILED (§15): the drop-依次同向 mutant did not disagree on a mixed case."


def main() -> int:
    _self_test()
    agg = {CONSOLIDATION: 0, TREND_UP: 0, TREND_DOWN: 0, MIXED: 0, NONE: 0}
    total = 0
    for seed in (11, 22, 33, 44, 55):
        h = run(40000, seed=seed)
        for k in agg:
            agg[k] += h[k]
        total += sum(h.values())
    # non-vacuity: 盘整, both 趋势 directions, AND mixed must all occur.
    for cls in (CONSOLIDATION, TREND_UP, TREND_DOWN, MIXED):
        assert agg[cls] > 0, f"non-vacuity: class {cls} never occurred — widen the generator"
    print(f"chanlun_trend_type OK: over {total} random 中枢 sequences, the 缠论 走势类型 classifier — "
          f"盘整 (=1 中枢) / 趋势 (≥2 依次同向 中枢, 上涨 if stepping up, 下跌 if down) — is TOTAL and "
          f"NEVER-SILENT (counts: {dict(agg)}): every 中枢-count/direction lands in exactly one of "
          f"{{consolidation, trend_up, trend_down, mixed, none}}; a ≥2-中枢 走势 that is NOT 依次同向 is the "
          f"NAMED residue `mixed` (needs a 级别 lift / is a larger 盘整), never a silent default. (DET) the "
          f"classifier is a pure function — 走势类型 唯一 PER GATE; (DIR) a 趋势 is genuinely monotone "
          f"(依次同向 enforced, not merely ≥2 中枢). It SITS ON the 中枢 (chanlun_zhongshu); on the reachable "
          f"domain the levels below are DETERMINISTIC (#1096), so 走势类型 inherits determinism, not multi-"
          f"valuedness — 确定性是 a 的派生性质 (a pinned on the reachable domain; threshold-0). §15: a "
          f"mutant calling any ≥2 中枢 a 趋势 disagrees with the honest classifier on a mixed case. NAMED "
          f"follow-ups: per-走势 DECOMPOSITION [chanlun_walk_decomposition_OPEN], 级别 lift "
          f"[chanlun_level_recursion_OPEN]. 数学才是唯一的判决.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
