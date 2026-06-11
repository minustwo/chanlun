/-
  Chanlun/StrokeUniqueness.lean

  缠论 Lemma 2 STRONG form — 笔 (Stroke) decomposition UNIQUENESS.

  ## What the 原文 claims

      所有的图形，都可以唯一地分解为上下交替的笔.
      (Any chart can be UNIQUELY decomposed into alternating 笔.)

  Alternation + separation are proven in `Chanlun/Stroke.lean`. This MWE adds
  the missing **uniqueness** — the determinacy verdict of Lemma 2.

  ## The structural spec — `IsValidBi`

  Defined recursively over the fractal list, parameterized by the current
  anchor (Option Fractal). The three branches of `step` (same-kind,
  opposite-far, opposite-close) lift directly to disjoint cases of
  `IsValidBi_from`.
-/

import Mathlib.Tactic
import Chanlun.Stroke

namespace Chanlun.StrokeUniqueness

open Chanlun.Stroke

/-! ## §1 — The structural spec `IsValidBi`. -/

def IsValidBi_from : Option Fractal → List Fractal → Int → List Stroke → Prop
  | _,        [],       _,    alt => alt = []
  | none,     f :: rest, δmin, alt => IsValidBi_from (some f) rest δmin alt
  | some a, f :: rest, δmin, alt =>
      if a.kind = f.kind then
        IsValidBi_from (some (pickRep a f)) rest δmin alt
      else if f.idx - a.idx ≥ δmin then
        ∃ rest_alt : List Stroke,
          alt = ⟨a.idx, f.idx, emitDir f⟩ :: rest_alt ∧
          IsValidBi_from (some f) rest δmin rest_alt
      else
        IsValidBi_from (some a) rest δmin alt

def IsValidBi (frs : List Fractal) (δmin : Int) (alt : List Stroke) : Prop :=
  IsValidBi_from none frs δmin alt

/-! ## §2 — The load-bearing lemma. -/

theorem fold_consumes_alt
    (δmin : Int) (frs : List Fractal) :
    ∀ (anchor : Option Fractal) (out₀ : List Stroke) (alt : List Stroke),
      IsValidBi_from anchor frs δmin alt →
      (frs.foldl (step δmin) ⟨anchor, out₀⟩).out = alt.reverse ++ out₀ := by
  induction frs with
  | nil =>
      intro anchor out₀ alt h
      simp [IsValidBi_from] at h
      subst h
      simp
  | cons f rest ih =>
      intro anchor out₀ alt h
      cases anchor with
      | none =>
          have h_step : step δmin ⟨none, out₀⟩ f = ⟨some f, out₀⟩ := by
            simp [step]
          simp only [List.foldl]
          rw [h_step]
          simp [IsValidBi_from] at h
          exact ih (some f) out₀ alt h
      | some a =>
          simp only [IsValidBi_from] at h
          by_cases h_kind : a.kind = f.kind
          · simp only [h_kind, if_true] at h
            have h_step : step δmin ⟨some a, out₀⟩ f =
                ⟨some (pickRep a f), out₀⟩ := by
              simp [step, h_kind]
            simp only [List.foldl]
            rw [h_step]
            exact ih (some (pickRep a f)) out₀ alt h
          · simp only [h_kind, if_false] at h
            by_cases h_gap : f.idx - a.idx ≥ δmin
            · simp only [h_gap, if_true] at h
              obtain ⟨rest_alt, h_alt, h_rest⟩ := h
              let stk : Stroke := ⟨a.idx, f.idx, emitDir f⟩
              have h_step : step δmin ⟨some a, out₀⟩ f =
                  ⟨some f, stk :: out₀⟩ := by
                simp [step, h_kind, h_gap]
              simp only [List.foldl]
              rw [h_step]
              have h_ih := ih (some f) (stk :: out₀) rest_alt h_rest
              rw [h_ih, h_alt]
              simp [List.reverse_cons]
            · simp only [h_gap, if_false] at h
              have h_step : step δmin ⟨some a, out₀⟩ f =
                  ⟨some a, out₀⟩ := by
                simp [step, h_kind, h_gap]
              simp only [List.foldl]
              rw [h_step]
              exact ih (some a) out₀ alt h

/-! ## §3 — Uniqueness (Lemma 2 strong). -/

/-- **THE UNIQUENESS THEOREM**. Any `IsValidBi` decomposition equals the
    canonical streaming output. Together with alternation + separation from
    `Chanlun.Stroke`, this completes the 原文 Lemma 2 claim
    *"所有的图形，都可以唯一地分解为上下交替的笔"*. -/
theorem strokes_unique
    (frs : List Fractal) (δmin : Int) (alt : List Stroke)
    (h : IsValidBi frs δmin alt) :
    alt = strokes frs δmin := by
  unfold IsValidBi at h
  have h_fold := fold_consumes_alt δmin frs none [] alt h
  have h_empty : (StrokeState.empty : StrokeState) = ⟨none, []⟩ := rfl
  rw [← h_empty] at h_fold
  simp at h_fold
  unfold strokes
  rw [h_fold]
  exact (List.reverse_reverse alt).symm

end Chanlun.StrokeUniqueness
