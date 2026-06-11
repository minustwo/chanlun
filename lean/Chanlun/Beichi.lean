/-
  Chanlun/Beichi.lean

  缠论 **背驰** (lessons 24/27/29/37) — 力度 (strength) comparison around
  the LAST 中枢. Lean MWE half of Klaus's parallel-cc dispatch
  (#1081 09:01:36Z + 09:09:56Z). Closes `[chanlun_beichi_lean_OPEN]`.

  Sequential pair with `ChanlunThirdBuysellMWE.lean` (this PR) — SAME zone
  algebra (Center {ZD, ZG} + directional element), now layering the 力度
  comparison on top of the BSP geometry.

  ## What 背驰 IS (lessons 24/29/37, from the host grounding)

  Compare the 力度 of the move LEAVING the last 中枢 (the 背驰段 C) against
  the same-direction move ENTERING it (A, the previous inter-中枢 travel).
  C weaker than A ⇒ **背驰** ⇒ the trend's continuation is failing ⇒
  第一类买卖点 territory (lesson 24).

  ## THE HONEST MEASURE QUESTION (lesson 27 + host grounding)

  The 原文 does NOT pin ONE 力度 measure. Two structurally natural
  integer-core measures (the host grounding tests BOTH and reports the
  agreement rate — 82.2% on the reachable domain, NOT a collapse — the
  measure choice is a REAL NAMED gate `[chanlun_beichi_measure_gate_OPEN]`):

  * **disp** — pure displacement: `C_disp` vs `A_disp` directly.
  * **slope** — displacement per element duration, integer-exact via
    cross-multiplication: `C_disp · A_len` vs `A_disp · C_len`.

  C weaker than A ⇒ 背驰; C stronger ⇒ no_beichi; equal ⇒ NAMED tie
  (never silently binned).

  ## The named theorems (Klaus's brief, target shapes)

  ```
  inductive BeichiVerdict | beichi | no_beichi | tie
  structure Move where lo hi : Int; dur : Nat
  def disp (m : Move) : Int := m.hi - m.lo
  inductive Measure | disp | slope
  def classifyBeichi : Move → Move → Measure → BeichiVerdict
  theorem classifyBeichi_total
  theorem beichi_irrefl                  -- under a strictly-positive move
  theorem beichi_load_bearing            -- the (disp·dur) cross-product strict ineq
  theorem beichi_measure_gate_witness    -- §15: disp and slope can disagree
  ```

  ## Honest scope (sub-residues, NOT in this MWE)

  * `[chanlun_beichi_measure_gate_OPEN]` — the disp-vs-slope gate is REAL
    (82.2% agreement on host grounding; NAMED, not collapsed). The
    `beichi_measure_gate_witness` theorem certifies non-vacuity.
  * `[chanlun_panzheng_beichi_OPEN]` — 盘整背驰 single-中枢 A-vs-C
    (lesson 37).
  * `[chanlun_beichi_macd_gate_OPEN]` — MACD as a measure-gate instance
    (lesson 27's 辅助 tool, explicitly named non-canonical).
  * `[chanlun_beichi_recursive_OPEN]` — 次级别 form on the proven 级别
    recursion.
  * `[chanlun_first_second_buysell_OPEN]` — 第一/第二类买卖点 sitting on
    top of this.

  ## Companion host grounding (Klaus arch-prep PR #1100 / commit 6e9d93db)

  `tools/mstnf_runtime/chanlun_beichi_grounding.py` — reachable 背驰
  windows over real raw → 包含处理 → 分型 → 笔 → 中枢 pipeline; disp/slope
  measures agree 82.2%; §15 mutant dropping the direction gate admits
  reversal windows (load-bearing).
-/

import Mathlib.Tactic

namespace Chanlun.Beichi

/-! ## §1 — Carriers. -/

/-- A directional move = displacement carrier with an explicit duration.
    Endpoints `lo ≤ hi` for an UP-move (interpreted bottom→top) by the
    extraction gate; `dur ≥ 1` (an inter-中枢 travel spans at least one
    element by the 中枢-disjointness lemma #1093). -/
structure Move where
  lo  : Int
  hi  : Int
  dur : Nat
  deriving Repr, DecidableEq

/-- Displacement of a move (lo→hi, integer-exact). -/
def disp (m : Move) : Int := m.hi - m.lo

/-- Positivity of a 背驰 input move — what the extraction gate guarantees
    (the host grounding's (POS) invariant: `a_disp > 0 ∧ a_len > 0`). -/
def Move.Pos (m : Move) : Prop := disp m > 0 ∧ m.dur > 0

/-- The 力度 measure — a NAMED gate (`[chanlun_beichi_measure_gate_OPEN]`),
    not a silent default. The 原文 leaves the measure choice open (lesson
    27 names MACD as an EXPLICITLY auxiliary instance). -/
inductive Measure where
  | disp  : Measure
  | slope : Measure
  deriving Repr, DecidableEq

/-- The 背驰 verdict — TOTAL over `{beichi, no_beichi, tie}`. `tie` is the
    equal-strength boundary, NAMED never silently binned (the host
    grounding's (TOTAL) invariant). -/
inductive BeichiVerdict where
  | beichi    : BeichiVerdict
  | no_beichi : BeichiVerdict
  | tie       : BeichiVerdict
  deriving Repr, DecidableEq

/-! ## §2 — The classifier (lesson 24/29 力度 comparison). -/

/-- The 力度 LHS / RHS pair under a NAMED measure. The slope measure is
    integer-exact via cross-multiplication (`a/b vs c/d ↔ a·d vs c·b` when
    `b, d > 0`) — no rationals needed. -/
def lhsRhs (a c : Move) : Measure → (Int × Int)
  | .disp  => (disp c, disp a)
  | .slope => (disp c * (a.dur : Int), disp a * (c.dur : Int))

/-- The 背驰 classifier. C weaker than A (`lhs < rhs`) ⇒ 背驰; stronger ⇒
    no_beichi; equal ⇒ NAMED tie. TOTAL + never-silent. -/
def classifyBeichi (a c : Move) (m : Measure) : BeichiVerdict :=
  let (lhs, rhs) := lhsRhs a c m
  if lhs < rhs then BeichiVerdict.beichi
  else if lhs > rhs then BeichiVerdict.no_beichi
  else BeichiVerdict.tie

/-! ## §3 — TOTAL: every input lands in exactly one verdict. -/

/-- **THEOREM (TOTAL)**: `classifyBeichi` is total and never silent. -/
theorem classifyBeichi_total (a c : Move) (m : Measure) :
    classifyBeichi a c m = BeichiVerdict.beichi ∨
    classifyBeichi a c m = BeichiVerdict.no_beichi ∨
    classifyBeichi a c m = BeichiVerdict.tie := by
  unfold classifyBeichi
  set p := lhsRhs a c m with h_p
  by_cases h_lt : p.1 < p.2
  · simp [h_lt]
  · simp only [h_lt, if_false]
    by_cases h_gt : p.1 > p.2
    · simp [h_gt]
    · simp [h_gt]

/-! ## §4 — IRREFLEXIVITY: a move is not 背驰 against itself. -/

/-- Auxiliary: the slope LHS/RHS are equal when comparing a move to itself
    (`disp a · a.dur = disp a · a.dur`). -/
theorem lhsRhs_self_eq (a : Move) (m : Measure) :
    (lhsRhs a a m).1 = (lhsRhs a a m).2 := by
  cases m with
  | disp  => rfl
  | slope => rfl

/-- **THEOREM (IRREFL)**: `classifyBeichi a a m ≠ beichi` for every move
    and measure — a move never 背驰s itself, regardless of measure. The
    integer cross-product form makes this trivial: the LHS/RHS coincide. -/
theorem beichi_irrefl (a : Move) (m : Measure) :
    classifyBeichi a a m ≠ BeichiVerdict.beichi := by
  unfold classifyBeichi
  have h_eq := lhsRhs_self_eq a m
  simp [h_eq]

/-! ## §5 — LOAD-BEARING: 背驰 IS the (disp·dur) cross-product strict
        inequality (the slope-measure substance). -/

/-- **THE LOAD-BEARING THEOREM (slope)**: under the slope measure, a
    `beichi` verdict means precisely the integer cross-product strict
    inequality `disp c · a.dur < disp a · c.dur`. This is the lesson-29
    转折的力度与级别 substance (matching the host grounding's
    `classify_beichi(_, "slope")` exactly). -/
theorem beichi_load_bearing_slope (a c : Move) :
    classifyBeichi a c Measure.slope = BeichiVerdict.beichi →
      disp c * (a.dur : Int) < disp a * (c.dur : Int) := by
  intro h
  unfold classifyBeichi at h
  simp only [lhsRhs] at h
  by_cases h_lt : disp c * (a.dur : Int) < disp a * (c.dur : Int)
  · exact h_lt
  · simp only [h_lt, if_false] at h
    by_cases h_gt : disp c * (a.dur : Int) > disp a * (c.dur : Int)
    · simp [h_gt] at h
    · simp [h_gt] at h

/-- **THE LOAD-BEARING THEOREM (disp)**: under the disp measure, a
    `beichi` verdict means precisely `disp c < disp a`. The simpler
    measure — the host grounding's `classify_beichi(_, "disp")` shape. -/
theorem beichi_load_bearing_disp (a c : Move) :
    classifyBeichi a c Measure.disp = BeichiVerdict.beichi →
      disp c < disp a := by
  intro h
  unfold classifyBeichi at h
  simp only [lhsRhs] at h
  by_cases h_lt : disp c < disp a
  · exact h_lt
  · simp only [h_lt, if_false] at h
    by_cases h_gt : disp c > disp a
    · simp [h_gt] at h
    · simp [h_gt] at h

/-- Combined statement matching Klaus's brief — `beichi_load_bearing`. -/
theorem beichi_load_bearing (a c : Move) :
    (classifyBeichi a c Measure.disp = BeichiVerdict.beichi →
        disp c < disp a) ∧
    (classifyBeichi a c Measure.slope = BeichiVerdict.beichi →
        disp c * (a.dur : Int) < disp a * (c.dur : Int)) :=
  ⟨beichi_load_bearing_disp a c, beichi_load_bearing_slope a c⟩

/-! ## §6 — NO_BEICHI converse: C stronger than A. -/

/-- A `no_beichi` verdict under disp means `disp c > disp a`. -/
theorem no_beichi_disp_strict (a c : Move) :
    classifyBeichi a c Measure.disp = BeichiVerdict.no_beichi →
      disp c > disp a := by
  intro h
  unfold classifyBeichi at h
  simp only [lhsRhs] at h
  by_cases h_lt : disp c < disp a
  · simp [h_lt] at h
  · simp only [h_lt, if_false] at h
    by_cases h_gt : disp c > disp a
    · exact h_gt
    · simp [h_gt] at h

/-- A `no_beichi` verdict under slope means `disp c · a.dur > disp a · c.dur`. -/
theorem no_beichi_slope_strict (a c : Move) :
    classifyBeichi a c Measure.slope = BeichiVerdict.no_beichi →
      disp c * (a.dur : Int) > disp a * (c.dur : Int) := by
  intro h
  unfold classifyBeichi at h
  simp only [lhsRhs] at h
  by_cases h_lt : disp c * (a.dur : Int) < disp a * (c.dur : Int)
  · simp [h_lt] at h
  · simp only [h_lt, if_false] at h
    by_cases h_gt : disp c * (a.dur : Int) > disp a * (c.dur : Int)
    · exact h_gt
    · simp [h_gt] at h

/-! ## §7 — MEASURE-GATE NON-VACUITY (§15): disp and slope can disagree. -/

/-- **THE MEASURE-GATE WITNESS**: there exist moves `a`, `c` where the
    disp measure says 背驰 but the slope measure says no_beichi. This is
    the constructive Lean witness of the host grounding's 82.2% agreement
    finding — the measure choice is a REAL NAMED gate
    `[chanlun_beichi_measure_gate_OPEN]`, not a redundant default.

    Hand-witness (matches the host grounding's `_self_test`): A travels
    10 over 5 elements (slope 2); C travels 6 over 1 element (slope 6).
    By disp: `6 < 10` ⇒ 背驰. By slope: `6·5=30 > 10·1=10` ⇒ no_beichi —
    C is shorter but FASTER. -/
theorem beichi_measure_gate_witness :
    ∃ (a c : Move),
      classifyBeichi a c Measure.disp = BeichiVerdict.beichi ∧
      classifyBeichi a c Measure.slope = BeichiVerdict.no_beichi := by
  refine ⟨⟨0, 10, 5⟩, ⟨0, 6, 1⟩, ?_, ?_⟩
  · -- disp: disp c = 6 < 10 = disp a
    unfold classifyBeichi
    simp [lhsRhs, disp]
  · -- slope: disp c · a.dur = 6·5=30 > 10·1=10 = disp a · c.dur
    unfold classifyBeichi
    simp [lhsRhs, disp]

/-! ## §8 — TIE characterization: equal strength. -/

/-- A `tie` verdict under disp means `disp c = disp a` (NAMED boundary
    residue, never silently binned into beichi or no_beichi). -/
theorem tie_disp_iff (a c : Move) :
    classifyBeichi a c Measure.disp = BeichiVerdict.tie →
      disp c = disp a := by
  intro h
  unfold classifyBeichi at h
  simp only [lhsRhs] at h
  by_cases h_lt : disp c < disp a
  · simp [h_lt] at h
  · simp only [h_lt, if_false] at h
    by_cases h_gt : disp c > disp a
    · simp [h_gt] at h
    · push_neg at h_lt h_gt
      omega

/-- A `tie` verdict under slope means the integer cross-product equality
    `disp c · a.dur = disp a · c.dur`. -/
theorem tie_slope_iff (a c : Move) :
    classifyBeichi a c Measure.slope = BeichiVerdict.tie →
      disp c * (a.dur : Int) = disp a * (c.dur : Int) := by
  intro h
  unfold classifyBeichi at h
  simp only [lhsRhs] at h
  by_cases h_lt : disp c * (a.dur : Int) < disp a * (c.dur : Int)
  · simp [h_lt] at h
  · simp only [h_lt, if_false] at h
    by_cases h_gt : disp c * (a.dur : Int) > disp a * (c.dur : Int)
    · simp [h_gt] at h
    · push_neg at h_lt h_gt
      omega

end Chanlun.Beichi
