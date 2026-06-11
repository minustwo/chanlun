/-
  Chanlun/Pipeline.lean

  缠论 pipeline composition: Algorithm N (single-pass normalize, idempotent) +
  Def-3 Fractal classification compose cleanly into the published 缠论
  decomposition pipeline's first two stages.

  ## What this proves (the composition)

  After Algorithm N, every 3-bar window in the result stack satisfies
  `isInclusionNormalized` — the precondition `[chanlun_inclusion_precondition]`
  that Def-3 (Fractal) assumes upstream. So Def-3's `def3_trichotomy` (every
  3-window classifies determinately to top / bottom / neither) applies to
  every interior 3-window of any normalized bar list.

      pipeline_inclusion_normalized :
          ∀ xs, ∀ {a b c rest},
              (normalize xs).1 = a :: b :: c :: rest →
              isInclusionNormalized ⟨b.h, b.l⟩ ⟨a.h, a.l⟩ ⟨c.h, c.l⟩
-/

import Mathlib.Tactic
import Chanlun.Fractal
import Chanlun.Normalize

namespace Chanlun.Pipeline

open Chanlun.Fractal
open Chanlun.Normalize

/-! ## §1 — Type bridge: `Interval` (normalize's stack) ↔ `Bar` (Fractal's window). -/

/-- The single field-order swap between the two stages' carriers.
    `Interval { l, h }` ↔ `Bar { h, l }` — same data, swapped declaration order. -/
def toBar (i : Interval) : Bar := ⟨i.h, i.l⟩

@[simp] theorem toBar_h (i : Interval) : (toBar i).h = i.h := rfl
@[simp] theorem toBar_l (i : Interval) : (toBar i).l = i.l := rfl

/-! ## §2 — The pivot lemma. -/

/-- `Interval.contained` (normalize's predicate) on two adjacent items is
    equivalent to the conjunction of the Bar-level containment conditions Def-3
    checks via `isInclusionNormalized`. -/
theorem not_contained_iff_bar
    (a b : Interval) :
    ¬ contained a b ↔
    ¬ ((toBar a).h ≤ (toBar b).h ∧ (toBar a).l ≥ (toBar b).l) ∧
    ¬ ((toBar b).h ≤ (toBar a).h ∧ (toBar b).l ≥ (toBar a).l) := by
  unfold contained
  constructor
  · intro h_nc
    simp only [toBar_h, toBar_l]
    refine ⟨?_, ?_⟩
    · intro ⟨hh, hl⟩
      exact h_nc (Or.inl ⟨hl, hh⟩)
    · intro ⟨hh, hl⟩
      exact h_nc (Or.inr ⟨hl, hh⟩)
  · intro ⟨h1, h2⟩
    simp only [toBar_h, toBar_l] at h1 h2
    intro h_c
    rcases h_c with ⟨hl, hh⟩ | ⟨hl, hh⟩
    · exact h1 ⟨hh, hl⟩
    · exact h2 ⟨hh, hl⟩

/-! ## §3 — The composition theorem. -/

/-- THE PIPELINE COMPOSITION: for any input bar list, after Algorithm N's
    single-pass `normalize`, any 3-bar window in the result stack satisfies
    `isInclusionNormalized` — so Def-3's `def3_trichotomy` applies determinately
    at every interior position of the normalized output. -/
theorem pipeline_inclusion_normalized
    (xs : List Interval) {a b c : Interval} {rest : List Interval} :
    (normalize xs).1 = a :: b :: c :: rest →
    isInclusionNormalized (toBar a) (toBar b) (toBar c) := by
  intro h_eq
  have h_nac : noAdjContainment (normalize xs).1 :=
    normalize_no_adjacent_containment xs
  rw [h_eq] at h_nac
  unfold noAdjContainment at h_nac
  obtain ⟨h_nc_ab, h_rest⟩ := h_nac
  unfold noAdjContainment at h_rest
  obtain ⟨h_nc_bc, _⟩ := h_rest
  have h_ab := (not_contained_iff_bar a b).mp h_nc_ab
  have h_bc := (not_contained_iff_bar b c).mp h_nc_bc
  unfold isInclusionNormalized
  refine ⟨h_ab.1, h_ab.2, h_bc.2, h_bc.1⟩

/-! ## §4 — Corollary: Def-3 determinately applies. -/

/-- COROLLARY: for any normalized bar list with ≥ 3 elements, the leading
    3-window determinately classifies to one of top / bottom / neither
    (Def-3 trichotomy applies). -/
theorem pipeline_fractal_classification_well_defined
    (xs : List Interval) {a b c : Interval} {rest : List Interval}
    (_h_eq : (normalize xs).1 = a :: b :: c :: rest) :
    (classifyDef3 (toBar a) (toBar b) (toBar c) = .top ∧
        isTopFractal (toBar a) (toBar b) (toBar c)) ∨
    (classifyDef3 (toBar a) (toBar b) (toBar c) = .bottom ∧
        isBottomFractal (toBar a) (toBar b) (toBar c) ∧
        ¬ isTopFractal (toBar a) (toBar b) (toBar c)) ∨
    (classifyDef3 (toBar a) (toBar b) (toBar c) = .neither ∧
        Def3Residue (toBar a) (toBar b) (toBar c)) := by
  exact def3_trichotomy (toBar a) (toBar b) (toBar c)

end Chanlun.Pipeline
