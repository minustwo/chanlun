"""中枢 (走势中枢, lesson 17/20) — the level above 线段, math-first.

★★ CORRECTION (Klaus 2026-06-11): the "zone-gate (first3 vs all) gate-relativity ~12%" claimed below is an
ARTIFACT of ARBITRARY [ZD,ZG] inputs. On the REACHABLE domain (real K-lines → 包含处理 → 分型 → 笔 → 中枢),
first3 and all COINCIDE (0 differ — see chanlun_bi_reachable_determinism_grounding). So the 中枢 zone choice
does NOT make 缠论 gate-relative on reachable data — 中枢 is DETERMINISTIC, like 笔. The construction +
VALID + DISJOINT results below are sound; only the gate-relativity INTERPRETATION is retracted (same lesson
as #1091: a math verdict must test the reachable domain, not arbitrary inputs). 数学才是唯一的判决.

The 缠论 完成 pipeline goes 分型→笔→线段→**中枢**→走势. The audit found 中枢 is NOT in the README
formal system (it stops at 线段). The 原文 (lesson 17): *某级别走势类型中，被至少三个连续次级别走势类型
所重叠的部分，称为缠中说禅走势中枢*. The zone (lesson 20, 第三类买卖点): ZG = 中枢 upper boundary,
ZD = 中枢 lower boundary, used by 三买/三卖 (离开中枢后回试不破 ZG/ZD).

Standard construction (over a sequence of alternating sub-elements — 笔 or 线段 under a CHOSEN gate, each
an integer price range [lo, hi]):
  - scan for ≥3 consecutive elements with a COMMON overlap: ZD = max(lows of the first 3),
    ZG = min(highs of the first 3); a 中枢 FORMS iff ZD ≤ ZG (genuine overlap).
  - EXTEND: subsequent elements that still overlap the 中枢 zone join it.
  - END: the first element that does NOT overlap the zone terminates the 中枢; the next 中枢 starts after.

GATE-FAMILY (the #1091 gate-relativity propagates UP): the 中枢 is built over a chosen 笔/线段 gate (lower
levels were already shown multivalued), AND the ZONE itself is a gate choice:
  (first3) the core zone [ZD,ZG] is FIXED by the first 3 elements (the standard 缠论 中枢区间);
  (all)    the zone is RE-tightened to the overlap of ALL members as they join (a stricter reading).
These DIFFER (a member that overlaps the first-3 core may not overlap the all-tightened core). So 中枢,
like 笔, is determinacy-RELATIVE-to-a-gate — 确定性是 a 的派生性质, all the way up.

THE MATH VERDICT (Klaus: 数学才是唯一的判决), asserted over random element sequences:
  (DET)      each (sequence, zone-gate) → a PURE function (re-run identical). 中枢 decomposition is
             deterministic FOR EACH GATE — so 缠论's 中枢 唯一性 holds per gate.
  (VALID)    every emitted 中枢 has ZD ≤ ZG (a genuine overlap region — never an empty/inverted zone).
  (DISJOINT) the 中枢s are INDEX-DISJOINT and ordered (center[k].end < center[k+1].start) — no element is
             in two 中枢s; the decomposition is a clean sub-partition, never double-counted.
  (GATE)     first3 ≠ all on a real fraction of sequences — the zone choice is a NAMED gate
             [chanlun_zhongshu_zone_gate_OPEN], the gate-relativity of #1091 carried to the 中枢 level.

§15 (the harness CAN fail): a MUTANT that emits a 中枢 from 3 NON-overlapping elements (ZD > ZG) MUST break
(VALID) — proving the overlap gate is load-bearing (a 中枢 is an OVERLAP, not any 3 elements). Non-vacuity:
the population must actually FORM 中枢s (≥3 overlapping) AND exhibit first3≠all, else the claims are vacuous.

HONEST SCOPE (named, not silent): this grounds 中枢 FORMATION + zone + the core determinacy/disjointness
over ONE level. Deeper 原文 rules are named follow-ups: 中枢延伸 vs 中枢新生 (the GG/DD 震荡区间 vs the
[ZD,ZG] core) [chanlun_zhongshu_extension_OPEN]; the 9-段 中枢升级 → higher-level 中枢
[chanlun_zhongshu_level_upgrade_OPEN]; 盘整(1中枢)/趋势(≥2依次同向中枢) [chanlun_trend_type_OPEN];
三类买卖点 via ZG/ZD [chanlun_three_buysell_OPEN]. Integer-core; elements carry the gate of the level below.
"""
from __future__ import annotations

import random
import sys


def zhongshu(els, zone: str = "first3"):
    """中枢 decomposition over a list of elements (each {idx, lo, hi}). `zone` ∈ {first3, all} is the
    NAMED zone gate. Returns a list of centers {start, end, ZD, ZG, n} (start/end = element indices)."""
    centers, i, n = [], 0, len(els)
    while i + 2 < n:
        ZD = max(els[i]["lo"], els[i + 1]["lo"], els[i + 2]["lo"])
        ZG = min(els[i]["hi"], els[i + 1]["hi"], els[i + 2]["hi"])
        if ZD <= ZG:                                    # the first 3 overlap → a 中枢 forms
            members = [i, i + 1, i + 2]
            zd, zg = ZD, ZG                             # the live overlap test zone
            j = i + 3
            while j < n and els[j]["lo"] <= zg and els[j]["hi"] >= zd:   # element j overlaps the zone
                members.append(j)
                if zone == "all":                       # (all) re-tighten the zone to ALL members
                    zd = max(zd, els[j]["lo"])
                    zg = min(zg, els[j]["hi"])
                j += 1
            centers.append({"start": i, "end": members[-1], "ZD": ZD, "ZG": ZG, "n": len(members)})
            i = members[-1] + 1                          # next 中枢 starts AFTER this one ends
        else:
            i += 1                                       # no 中枢 here — slide one element
    return centers


def _zhongshu_no_overlap_gate(els):
    """§15 MUTANT: forms a 中枢 from ANY 3 consecutive elements (drops the ZD≤ZG overlap gate). MUST
    produce a center with ZD > ZG when the 3 don't actually overlap — breaking (VALID)."""
    centers, i, n = [], 0, len(els)
    while i + 2 < n:
        ZD = max(els[i]["lo"], els[i + 1]["lo"], els[i + 2]["lo"])
        ZG = min(els[i]["hi"], els[i + 1]["hi"], els[i + 2]["hi"])
        centers.append({"start": i, "end": i + 2, "ZD": ZD, "ZG": ZG})   # BUG: no overlap check
        i += 3
    return centers


def _gen_elements(rng):
    """A random sequence of integer price-range elements (笔/线段 under some gate), drifting so that
    ≥3-overlap 中枢s actually form a meaningful fraction of the time (non-vacuity)."""
    n = rng.randint(0, 20)
    out, idx, base = [], 0, rng.randint(0, 100)
    for _ in range(n):
        idx += 1
        base += rng.randint(-6, 6)                       # gentle drift → frequent overlaps
        half = rng.randint(2, 9)
        out.append({"idx": idx, "lo": base - half, "hi": base + half})
    return out


def run(n: int, seed: int):
    rng = random.Random(seed)
    formed = gate_diff = total = 0
    for _ in range(n):
        els = _gen_elements(rng)
        c1 = zhongshu(els, "first3")
        ca = zhongshu(els, "all")
        # (DET) pure function per gate.
        assert zhongshu(els, "first3") == c1 and zhongshu(els, "all") == ca, \
            f"[DET seed={seed}] 中枢 not deterministic"
        for c in c1 + ca:
            # (VALID) genuine overlap region.
            assert c["ZD"] <= c["ZG"], f"[VALID seed={seed}] 中枢 with ZD={c['ZD']} > ZG={c['ZG']}"
        # (DISJOINT) ordered, index-disjoint within each gate.
        for centers in (c1, ca):
            for k in range(len(centers) - 1):
                assert centers[k]["end"] < centers[k + 1]["start"], \
                    f"[DISJOINT seed={seed}] 中枢s overlap: {centers[k]} then {centers[k+1]}"
            for c in centers:
                assert c["start"] <= c["end"] and c["n"] >= 3, f"[shape seed={seed}] bad center {c}"
        if c1:
            formed += 1
        if c1 != ca:
            gate_diff += 1                                # (GATE) first3 vs all differ — the zone gate
        total += 1
    return total, formed, gate_diff


def _self_test() -> None:
    # §15: the no-overlap-gate mutant MUST emit a ZD>ZG center on non-overlapping elements.
    els = [{"idx": 0, "lo": 0, "hi": 2}, {"idx": 1, "lo": 10, "hi": 12}, {"idx": 2, "lo": 20, "hi": 22}]
    mut = _zhongshu_no_overlap_gate(els)
    assert mut and mut[0]["ZD"] > mut[0]["ZG"], "§15 setup: mutant should make an inverted zone"
    assert zhongshu(els, "first3") == [], "honest 中枢 must NOT form on non-overlapping elements"
    # a hand 中枢: 3 overlapping elements around 50 → forms [ZD,ZG]; a 4th that overlaps extends it.
    els2 = [{"idx": 0, "lo": 45, "hi": 55}, {"idx": 1, "lo": 48, "hi": 58}, {"idx": 2, "lo": 44, "hi": 53},
            {"idx": 3, "lo": 49, "hi": 60}, {"idx": 4, "lo": 90, "hi": 99}]
    c = zhongshu(els2, "first3")
    assert len(c) == 1 and c[0]["ZD"] == 48 and c[0]["ZG"] == 53 and c[0]["end"] == 3, f"hand 中枢 wrong: {c}"
    # the 5th element (lo=90) leaves the zone [48,53] → not a member.


def main() -> int:
    _self_test()
    total = formed = gate_diff = 0
    for seed in (11, 22, 33, 44, 55):
        t, f, g = run(40000, seed=seed)
        total += t; formed += f; gate_diff += g
    assert formed >= total // 20, f"non-vacuity: only {formed}/{total} sequences formed a 中枢 — widen gen"
    assert gate_diff > 0, "non-vacuity: first3 and all NEVER differed — the zone gate is not exercised"
    print(f"chanlun_zhongshu OK: over {total} random element sequences ({formed} formed a 中枢), the 缠论 "
          f"走势中枢 construction (≥3 consecutive overlapping sub-elements → [ZD=max lows, ZG=min highs], "
          f"forms iff ZD≤ZG, extends while overlapping, ends when an element leaves) is, per zone-gate: "
          f"(DET) DETERMINISTIC (pure function — 中枢 唯一性 holds per gate), (VALID) every 中枢 has ZD≤ZG "
          f"(a genuine overlap, never inverted), (DISJOINT) 中枢s are index-disjoint + ordered (no element "
          f"in two 中枢s). (GATE) the zone choice first3-vs-all DIFFERS on {gate_diff}/{total} sequences — so "
          f"中枢, like 笔 (#1091), is determinacy-RELATIVE-to-a-gate [chanlun_zhongshu_zone_gate_OPEN]; the "
          f"gate-relativity propagates UP the pipeline (确定性是 a 的派生性质, all the way). §15: a mutant "
          f"dropping the overlap gate emits an inverted ZD>ZG 中枢. NAMED follow-ups: 中枢延伸/GG-DD "
          f"[chanlun_zhongshu_extension_OPEN], 9-段升级 [chanlun_zhongshu_level_upgrade_OPEN], 盘整/趋势 "
          f"[chanlun_trend_type_OPEN], 三类买卖点 [chanlun_three_buysell_OPEN]. 数学才是唯一的判决.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
