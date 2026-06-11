/-
  Chanlun/Fractal.lean

  缠论 (Chan) Definition 3 (分型 / Fractal): the operator-side slot predicate
  ≡ Def-3, plus the σ/ρ classification.

  ## Source of truth (NOT invented)

  `chanlun.pdf` / `chanlun_zh.pdf` Definition 3 (Fractal), over a normalized
  interval sequence X = (X₁,…,Xᵤ), each interval carrying H/L:

      Top fractal at i:     Hᵢ > Hᵢ₋₁ ∧ Hᵢ > Hᵢ₊₁ ∧ Lᵢ > Lᵢ₋₁ ∧ Lᵢ > Lᵢ₊₁
      Bottom fractal at i:  Lᵢ < Lᵢ₋₁ ∧ Lᵢ < Lᵢ₊₁ ∧ Hᵢ < Hᵢ₋₁ ∧ Hᵢ < Hᵢ₊₁
      (Lemma 1: every interior position is exactly one of top/bottom/neither.)

  ## q / a / σ / ρ map

    q (carrier)       : the 3-bar window (a, b, c) — a `Bar × Bar × Bar`.
    a (admissibility) : the Def-3 gate (top ∨ bottom). The "neither" interior
                        position is the negative.
    σ (representative): the classification `FractalKind`: top / bottom / neither.
    ρ (residue)       : non-admissible windows — classified as `.neither`,
                        a NAMED structural residue (never a silent label).

  ## Honest scope `[chanlun_inclusion_precondition]`

  Def-3 assumes the input window is INCLUSION-NORMALIZED (缠论's "包含关系"
  pre-processing collapses contained intervals into a single bar). This
  pre-processing is UPSTREAM of Def-3 and not part of the predicate itself.
  We name this precondition `[chanlun_inclusion_precondition]` and STATE
  it explicitly (`isInclusionNormalized`).
-/

import Mathlib.Tactic

namespace Chanlun.Fractal

/-! ## §1 — Carrier (q): the 3-bar window. -/

/-- A single bar: high `h` and low `l`. Integer-valued (tick units —
    real-valued price expressed as integer ticks). -/
structure Bar where
  h : Int
  l : Int
  deriving Repr, DecidableEq

/-- The classification labels for a 3-bar interior window. -/
inductive FractalKind
  | top
  | bottom
  | neither
  deriving Repr, DecidableEq

/-! ## §2 — Definition 3, transcribed. -/

/-- **Def-3 top fractal**: middle bar's high AND low are strictly above
    both neighbours' high and low respectively. -/
def isTopFractal (a b c : Bar) : Prop :=
  b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l

/-- **Def-3 bottom fractal**: middle bar's high AND low are strictly below
    both neighbours' high and low respectively. -/
def isBottomFractal (a b c : Bar) : Prop :=
  b.l < a.l ∧ b.l < c.l ∧ b.h < a.h ∧ b.h < c.h

instance decIsTopFractal (a b c : Bar) : Decidable (isTopFractal a b c) := by
  unfold isTopFractal; infer_instance

instance decIsBottomFractal (a b c : Bar) : Decidable (isBottomFractal a b c) := by
  unfold isBottomFractal; infer_instance

/-- The Def-3 classification: produces a `FractalKind` from a 3-bar window. -/
def classifyDef3 (a b c : Bar) : FractalKind :=
  if isTopFractal a b c then .top
  else if isBottomFractal a b c then .bottom
  else .neither

/-! ## §3 — The operator-side slot predicate (integer-coded). -/

/-- The operator-side slot classifier, integer-coded per the matchTag
    pipeline. Same Def-3 predicate; integer-coded output. -/
def fractalSlotPredicate (a b c : Bar) : Int :=
  if isTopFractal a b c then 0
  else if isBottomFractal a b c then 1
  else 2

/-- Codec: `FractalKind` → integer code. -/
def kindToInt : FractalKind → Int
  | .top     => 0
  | .bottom  => 1
  | .neither => 2

/-! ## §4 — The equivalence theorem: slot predicate ≡ Def-3. -/

/-- **`fractal_slot_equiv_def3`**: the operator-side slot predicate (the
    integer-coded classifier) equals the Def-3 classification encoded
    via `kindToInt`. Holds for EVERY 3-bar window — no precondition. -/
theorem fractal_slot_equiv_def3 (a b c : Bar) :
    fractalSlotPredicate a b c = kindToInt (classifyDef3 a b c) := by
  unfold fractalSlotPredicate classifyDef3
  by_cases ht : isTopFractal a b c
  · simp [ht, kindToInt]
  · simp [ht]
    by_cases hbf : isBottomFractal a b c
    · simp [hbf, kindToInt]
    · simp [hbf, kindToInt]

/-! ## §5 — The inclusion precondition. -/

/-- `isInclusionNormalized a b c`: neither neighbour's interval is
    contained in the middle (or vice versa). This is 缠论's "包含关系"
    pre-processing precondition that Def-3 assumes upstream. -/
def isInclusionNormalized (a b c : Bar) : Prop :=
  ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) ∧ ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) ∧
  ¬ (c.h ≤ b.h ∧ c.l ≥ b.l) ∧ ¬ (b.h ≤ c.h ∧ b.l ≥ c.l)

/-! ## §6 — Lift as an instance. -/

/-- The Def-3 admissibility gate: a 3-bar window is **admissible** as a
    structural pivot iff it satisfies the Def-3 top OR bottom predicate. -/
def Def3Admissible (a b c : Bar) : Prop :=
  isTopFractal a b c ∨ isBottomFractal a b c

instance decDef3Admissible (a b c : Bar) : Decidable (Def3Admissible a b c) := by
  unfold Def3Admissible; infer_instance

/-- The canonical representative (σ) of a Def-3 window. -/
def Def3Representative (a b c : Bar) : FractalKind := classifyDef3 a b c

/-- The structural residue (ρ): non-admissible windows are classified as
    `.neither` — a NAMED structural residue per the never-silent convention. -/
def Def3Residue (a b c : Bar) : Prop := ¬ Def3Admissible a b c

instance decDef3Residue (a b c : Bar) : Decidable (Def3Residue a b c) := by
  unfold Def3Residue; infer_instance

/-- **Determinacy / trichotomy**: every 3-bar window classifies to exactly
    one of {top, bottom, neither}. -/
theorem def3_trichotomy (a b c : Bar) :
    (classifyDef3 a b c = .top ∧ isTopFractal a b c) ∨
    (classifyDef3 a b c = .bottom ∧ isBottomFractal a b c
        ∧ ¬ isTopFractal a b c) ∨
    (classifyDef3 a b c = .neither ∧ Def3Residue a b c) := by
  unfold classifyDef3 Def3Residue Def3Admissible
  by_cases ht : isTopFractal a b c
  · exact Or.inl ⟨by simp [ht], ht⟩
  · by_cases hbf : isBottomFractal a b c
    · exact Or.inr (Or.inl ⟨by simp [ht, hbf], hbf, ht⟩)
    · refine Or.inr (Or.inr ⟨by simp [ht, hbf], ?_⟩)
      push_neg
      exact ⟨ht, hbf⟩

/-- **Soundness of the σ-classification**: an admissible window's
    representative is either `.top` or `.bottom` (never `.neither`). -/
theorem def3_admissible_classifies (a b c : Bar)
    (h : Def3Admissible a b c) :
    (Def3Representative a b c = .top ∧ isTopFractal a b c) ∨
    (Def3Representative a b c = .bottom ∧ isBottomFractal a b c) := by
  unfold Def3Representative classifyDef3
  rcases h with ht | hbf
  · exact Or.inl ⟨by simp [ht], ht⟩
  · by_cases ht : isTopFractal a b c
    · exact Or.inl ⟨by simp [ht], ht⟩
    · exact Or.inr ⟨by simp [ht, hbf], hbf⟩

/-- **Residue exhaustion** (the never-silent property at the σ level). -/
theorem def3_residue_iff_neither (a b c : Bar) :
    Def3Representative a b c = .neither ↔ Def3Residue a b c := by
  unfold Def3Representative classifyDef3 Def3Residue Def3Admissible
  by_cases ht : isTopFractal a b c
  · simp [ht]
  · by_cases hbf : isBottomFractal a b c
    · simp [ht, hbf]
    · simp [ht, hbf]

end Chanlun.Fractal
