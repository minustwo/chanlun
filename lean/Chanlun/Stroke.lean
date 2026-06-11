/-
  Chanlun/Stroke.lean

  缠论 Def-4 + Lemma 2 — 笔 (Stroke) stage. The leftmost-greedy stroke
  construction provably ALTERNATES (consecutive emits opposite-dir) and
  SEPARATES (every emit's index-gap ≥ δmin).

  ## Construction (host-grounded over 200k random fractal sequences)

  Fix `δmin ∈ ℤ`. Walk the fractal list with one alternating ANCHOR, leftmost-greedy:
    - no anchor yet              → set anchor to `f`
    - same-kind fractal           → keep the extremal representative (`pickRep`)
    - opposite-kind, idx-gap ≥ δmin → EMIT stroke (anchor → f), re-anchor to `f`
    - opposite-kind, too close    → drop (named 笔 residue)

  ## Load-bearing observation `stroke_emit_alternates_and_separates`

  An emit only happens in the opposite-kind+far branch, which re-anchors to `f`;
  the next emit starts from `f` (opposite of the old anchor's kind), so
  consecutive emits ALTERNATE (A) and each carries the `≥ δmin` gate (B).
-/

import Mathlib.Tactic

namespace Chanlun.Stroke

/-! ## §1 — Carriers. -/

inductive FractalKind | top | bottom
  deriving Repr, DecidableEq

inductive StrokeDir | up | down
  deriving Repr, DecidableEq

structure Fractal where
  idx  : Int
  kind : FractalKind
  h    : Int
  l    : Int
  deriving Repr, DecidableEq

structure Stroke where
  from_idx : Int
  to_idx   : Int
  dir      : StrokeDir
  deriving Repr, DecidableEq

/-! ## §2 — Construction primitives. -/

/-- Extremal representative among same-kind fractals (Def-4):
    top → higher `h`; bottom → lower `l`. -/
def pickRep (cur cand : Fractal) : Fractal :=
  match cur.kind with
  | .top    => if cand.h > cur.h then cand else cur
  | .bottom => if cand.l < cur.l then cand else cur

theorem pickRep_preserves_kind
    (cur cand : Fractal) (h_eq : cur.kind = cand.kind) :
    (pickRep cur cand).kind = cur.kind := by
  unfold pickRep
  cases hk : cur.kind with
  | top    =>
    by_cases h_h : cand.h > cur.h
    · simp [h_h]
      exact h_eq.symm.trans hk
    · simp [h_h]
      exact hk
  | bottom =>
    by_cases h_l : cand.l < cur.l
    · simp [h_l]
      exact h_eq.symm.trans hk
    · simp [h_l]
      exact hk

/-- Direction of a stroke emitted ending at `target`. -/
def emitDir (target : Fractal) : StrokeDir :=
  match target.kind with
  | .top    => .up
  | .bottom => .down

/-! ## §3 — The greedy fold state. -/

structure StrokeState where
  anchor : Option Fractal
  out    : List Stroke
  deriving Repr

def StrokeState.empty : StrokeState := { anchor := none, out := [] }

/-! ## §4 — One step. -/

def step (δmin : Int) (s : StrokeState) (f : Fractal) : StrokeState :=
  match s.anchor with
  | none =>
      { anchor := some f, out := s.out }
  | some a =>
      if a.kind = f.kind then
        { anchor := some (pickRep a f), out := s.out }
      else if f.idx - a.idx ≥ δmin then
        let stk : Stroke :=
          { from_idx := a.idx, to_idx := f.idx, dir := emitDir f }
        { anchor := some f, out := stk :: s.out }
      else
        s

/-! ## §5 — User-facing wrapper. -/

def strokes (frs : List Fractal) (δmin : Int) : List Stroke :=
  (frs.foldl (step δmin) StrokeState.empty).out.reverse

/-! ## §6 — Invariants. -/

def allSeparated (δmin : Int) (out : List Stroke) : Prop :=
  ∀ s ∈ out, δmin ≤ s.to_idx - s.from_idx

def allAlternate : List Stroke → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rs => a.dir ≠ b.dir ∧ allAlternate (b :: rs)

def anchorMatchesHead : Option Fractal → List Stroke → Prop
  | _,      []     => True
  | none,   _ :: _ => False
  | some a, h :: _ =>
      (h.dir = .up ∧ a.kind = .top) ∨ (h.dir = .down ∧ a.kind = .bottom)

def goodState (δmin : Int) (s : StrokeState) : Prop :=
  allSeparated δmin s.out ∧
  allAlternate s.out ∧
  anchorMatchesHead s.anchor s.out

theorem goodState_empty (δmin : Int) :
    goodState δmin StrokeState.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact absurd hx (List.not_mem_nil x)
  · show allAlternate ([] : List Stroke)
    unfold allAlternate
    trivial
  · show True; trivial

/-! ## §7 — `step` preserves `goodState`. -/

theorem step_preserves
    (δmin : Int) (s : StrokeState) (f : Fractal)
    (h : goodState δmin s) :
    goodState δmin (step δmin s f) := by
  obtain ⟨h_sep, h_alt, h_link⟩ := h
  unfold step
  match h_a : s.anchor with
  | none =>
    have h_out_nil : s.out = [] := by
      cases h_out : s.out with
      | nil       => rfl
      | cons hd tl =>
        exfalso
        rw [h_a, h_out] at h_link
        exact h_link
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; rw [h_out_nil] at hx; simp at hx
    · rw [h_out_nil]; simp [allAlternate]
    · rw [h_out_nil]
      show True; trivial
  | some a =>
    by_cases h_kind : a.kind = f.kind
    · simp only [h_kind, if_true]
      refine ⟨h_sep, h_alt, ?_⟩
      cases h_out : s.out with
      | nil       => show True; trivial
      | cons hd tl =>
        rw [h_a, h_out] at h_link
        have h_pr_kind : (pickRep a f).kind = a.kind :=
          pickRep_preserves_kind a f h_kind
        rcases h_link with ⟨h_d, h_k⟩ | ⟨h_d, h_k⟩
        · exact Or.inl ⟨h_d, by rw [h_pr_kind]; exact h_k⟩
        · exact Or.inr ⟨h_d, by rw [h_pr_kind]; exact h_k⟩
    · simp only [h_kind, if_false]
      by_cases h_gap : f.idx - a.idx ≥ δmin
      · simp only [h_gap, if_true]
        let stk : Stroke := { from_idx := a.idx, to_idx := f.idx, dir := emitDir f }
        have h_sep_new : allSeparated δmin (stk :: s.out) := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hin
          · exact h_gap
          · exact h_sep x hin
        have h_alt_new : allAlternate (stk :: s.out) := by
          cases h_out : s.out with
          | nil       => simp [allAlternate]
          | cons hd tl =>
            refine ⟨?_, ?_⟩
            · rw [h_a, h_out] at h_link
              show stk.dir ≠ hd.dir
              rcases h_link with ⟨hd_dir, a_top⟩ | ⟨hd_dir, a_bot⟩
              · have h_fbot : f.kind = .bottom := by
                  cases hf : f.kind with
                  | top    => rw [a_top, hf] at h_kind; exact absurd rfl h_kind
                  | bottom => rfl
                have h_stk_down : stk.dir = .down := by
                  show emitDir f = .down
                  simp [emitDir, h_fbot]
                rw [h_stk_down, hd_dir]; intro hcontra; cases hcontra
              · have h_ftop : f.kind = .top := by
                  cases hf : f.kind with
                  | top    => rfl
                  | bottom => rw [a_bot, hf] at h_kind; exact absurd rfl h_kind
                have h_stk_up : stk.dir = .up := by
                  show emitDir f = .up
                  simp [emitDir, h_ftop]
                rw [h_stk_up, hd_dir]; intro hcontra; cases hcontra
            · rw [h_out] at h_alt; exact h_alt
        have h_link_new : anchorMatchesHead (some f) (stk :: s.out) := by
          show (stk.dir = .up ∧ f.kind = .top) ∨ (stk.dir = .down ∧ f.kind = .bottom)
          cases hf : f.kind with
          | top    => exact Or.inl ⟨by simp [emitDir, hf], rfl⟩
          | bottom => exact Or.inr ⟨by simp [emitDir, hf], rfl⟩
        exact ⟨h_sep_new, h_alt_new, h_link_new⟩
      · simp only [h_gap, if_false]
        exact ⟨h_sep, h_alt, h_link⟩

/-! ## §8 — The final theorems. -/

theorem foldl_step_goodState
    (δmin : Int) (frs : List Fractal) :
    goodState δmin (frs.foldl (step δmin) StrokeState.empty) := by
  suffices h : ∀ (s : StrokeState),
      goodState δmin s →
      goodState δmin (frs.foldl (step δmin) s) by
    exact h StrokeState.empty (goodState_empty δmin)
  intro s h_good
  induction frs generalizing s with
  | nil       => simpa using h_good
  | cons x xs ih =>
    simp only [List.foldl]
    exact ih _ (step_preserves δmin s x h_good)

/-- **SEPARATION (B)**: every emitted stroke has gap ≥ δmin. -/
theorem stroke_emits_separated (frs : List Fractal) (δmin : Int) :
    allSeparated δmin (frs.foldl (step δmin) StrokeState.empty).out :=
  (foldl_step_goodState δmin frs).1

/-- **ALTERNATION (A)**: consecutive emits have opposite direction. -/
theorem stroke_emits_alternate (frs : List Fractal) (δmin : Int) :
    allAlternate (frs.foldl (step δmin) StrokeState.empty).out :=
  (foldl_step_goodState δmin frs).2.1

/-! ## §9 — The output-order wrapper. -/

theorem strokes_separated (frs : List Fractal) (δmin : Int) :
    allSeparated δmin (strokes frs δmin) := by
  intro x hx
  unfold strokes at hx
  rw [List.mem_reverse] at hx
  exact stroke_emits_separated frs δmin x hx

end Chanlun.Stroke
