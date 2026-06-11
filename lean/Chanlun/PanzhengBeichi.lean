/-
  Chanlun/PanzhengBeichi.lean

  缠论 **盘整背驰** (lesson 37) — the SINGLE-中枢 INTRA force comparison.
  Closes `[chanlun_panzheng_beichi_lean_OPEN]` (queue item 4 of Klaus's
  FULL 缠论 ownership mandate #1081, sits alongside #1107's
  第一/第二类买卖点; together with the 趋势背驰 of PR #1104 these are
  the two halves of lesson 37: 趋势 INTER-中枢 vs 盘整 INTRA-中枢).

  ## What 原文 says (lesson 37, paraphrased)

      在一个中枢内部，进入段 (A-segment) 与离开段 (C-segment) 的力度
      比较：若 力度(A) > 力度(C)，则该 C-离开 是盘整背驰，中枢将延伸
      到新高(上中枢) / 新低(下中枢)。

  Reading the 原文 mathematically (host grounding
  `tools/mstnf_runtime/chanlun_panzheng_beichi_grounding.py` is the math
  source of truth):

  * **panzheng_beichi** ⇔ inside a single 中枢, 力度(C) < 力度(A) under
    the chosen NAMED measure. The C-exit is structurally weaker than the
    A-enter — the 中枢 will likely 延伸.
  * **no_panzheng_beichi** ⇔ C is at least as strong as A — the 中枢
    does NOT exhibit a 盘整背驰 at this triple.
  * **tie** ⇔ equal strength — NAMED boundary (the 原文-literal integer
    boundary, never silently binned into either side).
  * **incomplete** ⇔ the 中枢 has no net direction (last.hi == first.hi
    AND last.lo == first.lo — perfectly balanced); the d = 0 case is the
    NAMED residue, never silent.

  ## Re-use of the 趋势背驰 algebra (PR #1104)

  The 力度 algebra (`lhsRhs` + the `lhs < rhs ⇒ 背驰` rule under measure
  m ∈ {disp, slope}) is IDENTICAL to the 趋势背驰 reading of #1104; the
  only difference is the COMPARISON DOMAIN — INTRA-中枢 here, INTER-中枢
  there. We re-state the `Move` carrier + `Measure` enum + `disp`/`lhsRhs`/
  `isBeichi` for self-containment (#1104 is a separate PR not yet merged
  on this branch), mirroring the same shape `ChanlunFirstSecondBuysellMWE`
  used.

  ## The named theorems

  * `classify_panzheng_total` — TOTAL + never-silent over the four
    PanzhengVerdict classes.
  * `panzheng_load_bearing_disp` — soundness: `panzheng_beichi` under
    `disp` ⇒ `disp c.c < disp c.a` (the C-exit IS measurably weaker).
  * `panzheng_load_bearing_slope` — soundness under `slope`.
  * `panzheng_measure_gate_witness` — a constructive divergence
    witness: there exist `a, c` for which `disp` says `panzheng_beichi`
    and `slope` says `no_panzheng_beichi`. This certifies the abstract
    measure-gate algebra (even though, on the SINGLE-元素 reading where
    A_len = C_len = 1 the per-element disp = slope at the algebra level,
    the gate is STRUCTURALLY available — the witness uses A_len ≠ C_len
    which the LIFTED form below admits).
  * `panzheng_incomplete_iff` — the d = 0 (balanced 中枢) NAMED residue
    surface.

  ## Honest scope — named sub-residues (not in this MWE)

  * `[chanlun_panzheng_measure_gate_propagation_OPEN]` — host grounding
    shows the disp-vs-slope measure gate COLLAPSES (0 divergence on
    5022 reachable per-element single-中枢 triples) because the SINGLE-
    元素 reading forces A_len = C_len = 1. The structural witness here
    uses the GENERAL lifted form (A_len ≠ C_len allowed). When future
    work generalizes the host grounding to multi-元素 A and C sub-runs
    (e.g. via the 9-段 中枢升级), the measure gate is expected to
    open up.
  * `[chanlun_panzheng_beichi_recursive_OPEN]` — 次级别 form on the
    proven 级别 recursion (#1097/#1101).
  * `[chanlun_panzheng_beichi_first_second_OPEN]` — combined with
    第一/第二类买卖点 (#1107) for the single-中枢 BSP form.

  ## Companion host grounding (queue item 4 of #1081)

  `tools/mstnf_runtime/chanlun_panzheng_beichi_grounding.py` — 5022
  reachable INTRA-中枢 triples from REAL flat-biased regime-switching
  K-lines (real normalize+分型+笔+中枢). disp histogram:
  panzheng_beichi 920 / no_panzheng_beichi 3987 / tie 115 /
  incomplete 302. The measure-gate STRUCTURALLY COLLAPSES on the
  single-元素 reading (0 divergence; A_len = C_len = 1 forces
  disp = slope algebraically). §15 INTER-CENTER measure mutant
  disagreed on 9814 triples (the INTRA-vs-INTER choice IS the
  load-bearing content of lesson 37).
-/

import Mathlib.Tactic

namespace Chanlun.PanzhengBeichi

/-! ## §1 — Carriers (self-contained; mirror #1104 / #1107 shape). -/

/-- A directional move (the 力度 carrier), same shape as
    `ChanlunFirstSecondBuysellMWE.Move`. Endpoints `lo ≤ hi`; `dur ≥ 1`. -/
structure Move where
  lo  : Int
  hi  : Int
  dur : Nat
  deriving Repr, DecidableEq

/-- Displacement of a move (integer-exact). -/
def disp (m : Move) : Int := m.hi - m.lo

/-- The 力度 measure — a NAMED gate. -/
inductive Measure where
  | disp  : Measure
  | slope : Measure
  deriving Repr, DecidableEq

/-- A 中枢 (zone-only — for the 盘整背驰 verdict we only need direction). -/
structure Center where
  ZD : Int  -- 下沿
  ZG : Int  -- 上沿
  deriving Repr, DecidableEq

/-- The 盘整背驰 verdict — TOTAL over four NAMED classes. -/
inductive PanzhengVerdict where
  | panzheng_beichi    : PanzhengVerdict
  | no_panzheng_beichi : PanzhengVerdict
  | tie                : PanzhengVerdict
  | incomplete         : PanzhengVerdict
  deriving Repr, DecidableEq

/-- The PanzhengTriple the classifier sees: a 中枢 `center`, the A-enter
    move + the C-exit move + a direction `d` (+1 up / -1 down / 0
    incomplete). The host grounding's `panzheng_triple` extractor is the
    semantic source (first sub-element vs last sub-element with the
    中枢's net drift as `d`); here `d` is a parameter input. -/
structure PanzhengTriple where
  center : Center
  a      : Move
  c      : Move
  d      : Int  -- +1 up-中枢 / -1 down-中枢 / 0 incomplete
  deriving Repr

/-! ## §2 — The 力度 LHS/RHS pair (re-stated from #1104). -/

/-- The 力度 LHS / RHS pair — same algebra as `ChanlunBeichiMWE.lhsRhs`. -/
def lhsRhs (a c : Move) : Measure → (Int × Int)
  | .disp  => (disp c, disp a)
  | .slope => (disp c * (a.dur : Int), disp a * (c.dur : Int))

/-- C weaker than A (`lhs < rhs`) ⇒ 背驰. -/
def isBeichi (a c : Move) (m : Measure) : Bool :=
  let (lhs, rhs) := lhsRhs a c m
  decide (lhs < rhs)

/-- Tie (`lhs == rhs`). -/
def isTie (a c : Move) (m : Measure) : Bool :=
  let (lhs, rhs) := lhsRhs a c m
  decide (lhs = rhs)

/-! ## §3 — The 盘整背驰 classifier (TOTAL, never-silent). -/

/-- The lesson-37 盘整背驰 classifier. The chain:
    1. If `d = 0` ⇒ incomplete (the 中枢 has no net direction — NAMED).
    2. Else under measure `m`: if `lhs < rhs` ⇒ panzheng_beichi (C weaker);
       if `lhs = rhs` ⇒ tie (NAMED equal-strength boundary); else ⇒
       no_panzheng_beichi. -/
def classifyPanzheng (t : PanzhengTriple) (m : Measure) : PanzhengVerdict :=
  if t.d = 0 then
    PanzhengVerdict.incomplete
  else
    let (lhs, rhs) := lhsRhs t.a t.c m
    if lhs < rhs then PanzhengVerdict.panzheng_beichi
    else if lhs = rhs then PanzhengVerdict.tie
    else PanzhengVerdict.no_panzheng_beichi

/-! ## §4 — TOTAL: every input lands in exactly one named PanzhengVerdict. -/

/-- **THEOREM (TOTAL)**: `classifyPanzheng` is total and never silent. -/
theorem classify_panzheng_total (t : PanzhengTriple) (m : Measure) :
    classifyPanzheng t m = PanzhengVerdict.panzheng_beichi ∨
    classifyPanzheng t m = PanzhengVerdict.no_panzheng_beichi ∨
    classifyPanzheng t m = PanzhengVerdict.tie ∨
    classifyPanzheng t m = PanzhengVerdict.incomplete := by
  unfold classifyPanzheng
  by_cases h_d : t.d = 0
  · simp [h_d]
  · simp only [h_d, if_false]
    set lhs := (lhsRhs t.a t.c m).1
    set rhs := (lhsRhs t.a t.c m).2
    by_cases h_lt : lhs < rhs
    · simp [h_lt]
    · simp only [h_lt, if_false]
      by_cases h_eq : lhs = rhs
      · simp [h_eq]
      · simp [h_eq]

/-! ## §5 — INCOMPLETE characterization. -/

/-- **THEOREM**: `incomplete` ⇔ `d = 0` (the balanced-中枢 NAMED residue). -/
theorem panzheng_incomplete_iff (t : PanzhengTriple) (m : Measure) :
    classifyPanzheng t m = PanzhengVerdict.incomplete ↔ t.d = 0 := by
  unfold classifyPanzheng
  constructor
  · intro h
    by_cases h_d : t.d = 0
    · exact h_d
    · exfalso
      simp only [h_d, if_false] at h
      set lhs := (lhsRhs t.a t.c m).1
      set rhs := (lhsRhs t.a t.c m).2
      by_cases h_lt : lhs < rhs
      · simp [h_lt] at h
      · simp only [h_lt, if_false] at h
        by_cases h_eq : lhs = rhs
        · simp [h_eq] at h
        · simp [h_eq] at h
  · intro h_d
    simp [h_d]

/-! ## §6 — Load-bearing soundness (per measure). -/

/-- **THEOREM (LOAD-BEARING, DISP)**: `panzheng_beichi` under `disp` ⇒ the
    C-displacement is strictly less than the A-displacement (the C-exit
    is measurably weaker — the substantive content of lesson 37). -/
theorem panzheng_load_bearing_disp (t : PanzhengTriple) :
    classifyPanzheng t Measure.disp = PanzhengVerdict.panzheng_beichi →
      disp t.c < disp t.a ∧ t.d ≠ 0 := by
  intro h
  unfold classifyPanzheng at h
  by_cases h_d : t.d = 0
  · simp [h_d] at h
  · simp only [h_d, if_false] at h
    simp only [lhsRhs] at h
    by_cases h_lt : disp t.c < disp t.a
    · exact ⟨h_lt, h_d⟩
    · simp only [h_lt, if_false] at h
      by_cases h_eq : disp t.c = disp t.a
      · simp [h_eq] at h
      · simp [h_eq] at h

/-- **THEOREM (LOAD-BEARING, SLOPE)**: `panzheng_beichi` under `slope` ⇒
    the slope-comparison `disp c * a.dur < disp a * c.dur` (integer-exact
    cross-multiplication; the well-known faster-but-shorter case). -/
theorem panzheng_load_bearing_slope (t : PanzhengTriple) :
    classifyPanzheng t Measure.slope = PanzhengVerdict.panzheng_beichi →
      disp t.c * (t.a.dur : Int) < disp t.a * (t.c.dur : Int) ∧ t.d ≠ 0 := by
  intro h
  unfold classifyPanzheng at h
  by_cases h_d : t.d = 0
  · simp [h_d] at h
  · simp only [h_d, if_false] at h
    simp only [lhsRhs] at h
    by_cases h_lt : disp t.c * (t.a.dur : Int) < disp t.a * (t.c.dur : Int)
    · exact ⟨h_lt, h_d⟩
    · simp only [h_lt, if_false] at h
      by_cases h_eq : disp t.c * (t.a.dur : Int) = disp t.a * (t.c.dur : Int)
      · simp [h_eq] at h
      · simp [h_eq] at h

/-! ## §7 — THE MEASURE-GATE WITNESS (constructive divergence). -/

/-- **THEOREM (MEASURE-GATE WITNESS)**: there exists a `PanzhengTriple`
    for which `disp` says `panzheng_beichi` and `slope` says
    `no_panzheng_beichi`. This is the abstract algebra's load-bearing
    statement — the measure gate IS structurally available; the host
    grounding's collapse (0 divergence on the single-元素 reading) is
    because A_len = C_len = 1 forces the slope cross-product to equal
    the disp comparison.

    Construction: a = ⟨0, 10, 5⟩ (slope 2), c = ⟨0, 6, 1⟩ (slope 6). By
    disp: 6 < 10 ⇒ panzheng_beichi. By slope: 6*5 = 30 > 10*1 = 10 ⇒
    no_panzheng_beichi. d = +1 (any non-zero direction). -/
theorem panzheng_measure_gate_witness :
    ∃ (t : PanzhengTriple),
      classifyPanzheng t Measure.disp = PanzhengVerdict.panzheng_beichi ∧
      classifyPanzheng t Measure.slope = PanzhengVerdict.no_panzheng_beichi := by
  refine ⟨{ center := ⟨0, 100⟩
          , a := ⟨0, 10, 5⟩
          , c := ⟨0, 6, 1⟩
          , d := 1 }, ?_, ?_⟩
  · -- disp branch: 6 < 10 ⇒ panzheng_beichi
    unfold classifyPanzheng
    simp [lhsRhs, disp]
  · -- slope branch: 6*5 = 30 > 10*1 = 10 ⇒ no_panzheng_beichi
    unfold classifyPanzheng
    simp [lhsRhs, disp]

/-! ## §8 — The INTRA vs INTER load-bearing distinction (lesson 37). -/

/-- The §15 mutant — uses an INTER-中枢 measure on a SINGLE-中枢 triple
    (which is structurally degenerate: there is no inter-zone travel
    within one 中枢). Formalized as `classifyPanzheng` with both moves
    zeroed-out (the inter-zone travel within a single 中枢 is 0). -/
def classifyPanzheng_inter_mutant (t : PanzhengTriple) (_m : Measure) :
    PanzhengVerdict :=
  if t.d = 0 then PanzhengVerdict.incomplete
  else
    -- The mutant collapses INTRA strengths to 0 — simulating INTER-中枢
    -- travel within a single 中枢. lhs = rhs = 0 ⇒ tie always.
    let lhs : Int := 0
    let rhs : Int := 0
    if lhs < rhs then PanzhengVerdict.panzheng_beichi
    else if lhs = rhs then PanzhengVerdict.tie
    else PanzhengVerdict.no_panzheng_beichi

/-- **THEOREM (INTRA vs INTER LOAD-BEARING)**: there exists a triple where
    the honest INTRA classifier says `panzheng_beichi` but the INTER
    mutant says `tie` — the INTRA-vs-INTER choice IS the substantive
    content of lesson 37 (盘整背驰 = INTRA, 趋势背驰 = INTER). -/
theorem panzheng_intra_vs_inter_load_bearing :
    ∃ (t : PanzhengTriple) (m : Measure),
      classifyPanzheng t m = PanzhengVerdict.panzheng_beichi ∧
      classifyPanzheng_inter_mutant t m = PanzhengVerdict.tie := by
  refine ⟨{ center := ⟨0, 100⟩
          , a := ⟨0, 10, 1⟩
          , c := ⟨0, 4, 1⟩
          , d := 1 }, Measure.disp, ?_, ?_⟩
  · unfold classifyPanzheng
    simp [lhsRhs, disp]
  · unfold classifyPanzheng_inter_mutant
    simp

end Chanlun.PanzhengBeichi
