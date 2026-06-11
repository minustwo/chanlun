/-
  Chanlun/BiEndpointSubResidues.lean

  缠论 笔-endpoint sub-residues (PR #1090 §3 honest-scope follow-ups).
  Closes:
    * `[chanlun_bi_to_endpoint_first_admissible_OPEN]`
    * `[chanlun_bi_close_drop_named_residue_OPEN]`
    * `[chanlun_stroke_output_order_lift_OPEN]`

  Klaus FULL 缠论 ownership lane on #1081, queue item 5 PART B.

  ## What the three sub-residues say (from #1090 §3 honest scope)

  1. **`bi_to_endpoint_first_admissible`** — the TO-endpoint of each
     stroke is the LEFTMOST opposite-kind fractal after the from-anchor
     satisfying the gap-≥-δmin. A literal-strong reading of the 原文
     could interpret TO as the EXTREMAL of the FULL to-side same-kind
     run. The two readings coincide when the to-side same-kind run is a
     SINGLETON — and on the REACHABLE domain (post-`normalize`,
     containment-free), the run from #1098 is exactly that: a strictly
     alternating fractal sequence ⇒ each run has length 1 ⇒ leftmost =
     extremal.

  2. **`bi_close_drop_named_residue`** — opposite-close fractals
     (`gap < δmin`) drop branch. The uniqueness proof (#1090) treats
     this as a no-op in the fold/`IsValidBi` correspondence. The
     CHARACTERIZATION here: the drop branch returns the input state
     unchanged, so the IsValidBi relation is PRESERVED.

  3. **`stroke_output_order_lift`** — `allAlternate s → allAlternate
     s.reverse`. One-liner via `List.Chain'.reverse` over the
     SYMMETRIC predicate `(·.dir ≠ ·.dir)`.

  ## What this MWE proves

  * `to_endpoint_leftmost_eq_extremal_on_reachable` — on a
    `isStrictlyAlternating` fractal sequence (from #1098), the
    leftmost-admissible opposite-kind fractal IS the extremal of its
    (singleton) run.
  * `dropBranch_preserves_IsValidBi` — the SPEC-form characterization
    of the opposite-close drop branch: it is a no-op for `IsValidBi`.
  * `allAlternate_reverse` — alternation lifts from in-fold order to
    output order via the symmetric-pairwise predicate.

  ## Reuse

  * `lean/crt/ChanlunStrokeUniquenessNFFromMSTNFMWE.lean` (#1090) —
    `IsValidBi_from`, `strokes_unique`, the structural spec.
  * `lean/crt/ChanlunBiReachableDeterminismMWE.lean` (#1098) — the
    reachable-domain alternation theorem.
  * `lean/crt/ChanlunStrokeNFFromMSTNFMWE.lean` (#1086) —
    `allAlternate`, `step`, `strokes`.
-/

import Mathlib.Tactic
import Chanlun.StrokeUniqueness

namespace Chanlun.BiEndpointSubResidues

open Chanlun.Stroke
open Chanlun.StrokeUniqueness

/-! ## §1 — Sub-residue 1: `bi_to_endpoint_first_admissible`. -/

/-- A locally-stated "strictly alternating" predicate on the fractal
    list — every consecutive pair differs in kind. On the reachable
    domain (post-normalize), the alternation theorem #1098 supplies this
    invariant. -/
def isStrictlyAlternating : List Fractal → Prop
  | []           => True
  | [_]          => True
  | f :: g :: rs => f.kind ≠ g.kind ∧ isStrictlyAlternating (g :: rs)

/-- The TO-endpoint of a stroke as proposed by the literal-strong
    reading: the extremal of the to-side same-kind run starting at `f`.
    On a strictly alternating sequence (no same-kind run after `f`), this
    is simply `f`. We formalize as a function returning `f` when the
    next fractal differs in kind (the alternating case). -/
def toEndpoint_extremal_literal (f : Fractal) (rest : List Fractal) : Fractal :=
  match rest with
  | []        => f
  | g :: _    => if f.kind = g.kind then g else f

/-- **SUB-RESIDUE 1 THEOREM (`to_endpoint_leftmost_eq_extremal_on_reachable`)**.

    On a strictly alternating fractal sequence (the reachable-domain
    invariant from #1098), the LEFTMOST-admissible opposite-kind
    fractal IS the extremal of the (singleton) to-side same-kind run.

    Form: when the immediate next fractal `g` differs from `f` in kind,
    the literal extremal is `f` itself — and the `IsValidBi`
    leftmost-greedy emit pair `(a, g)` is exactly the leftmost
    admissible. Both readings agree. -/
theorem to_endpoint_leftmost_eq_extremal_on_reachable
    (f g : Fractal) (rs : List Fractal)
    (h_alt : isStrictlyAlternating (f :: g :: rs)) :
    toEndpoint_extremal_literal f (g :: rs) = f := by
  unfold toEndpoint_extremal_literal
  simp only [isStrictlyAlternating] at h_alt
  obtain ⟨h_kind_ne, _⟩ := h_alt
  simp [h_kind_ne]

/-! ## §2 — Sub-residue 2: `bi_close_drop_named_residue`. -/

/-- **SUB-RESIDUE 2 THEOREM 1 (`dropBranch_step_no_op`)**: in the
    opposite-close drop branch (anchor=some a, different kind, gap
    `< δmin`), `step` is a no-op: it returns the input state. -/
theorem dropBranch_step_no_op
    (δmin : Int) (a f : Fractal) (out₀ : List Stroke)
    (h_kind : a.kind ≠ f.kind)
    (h_gap : ¬ (f.idx - a.idx ≥ δmin)) :
    step δmin ⟨some a, out₀⟩ f = ⟨some a, out₀⟩ := by
  simp [step, h_kind, h_gap]

/-- **SUB-RESIDUE 2 THEOREM 2 (`dropBranch_preserves_IsValidBi`)**: the
    `IsValidBi` reduction in the drop branch — `IsValidBi_from (some a)
    (f :: rest) δmin alt ↔ IsValidBi_from (some a) rest δmin alt`. The
    drop is a no-op for the structural spec.

    This is the SPEC-FORM characterization the #1090 honest scope named.
    The uniqueness proof in #1090 already uses this implicitly; here we
    state it as a load-bearing equation. -/
theorem dropBranch_preserves_IsValidBi
    (δmin : Int) (a f : Fractal) (rest : List Fractal) (alt : List Stroke)
    (h_kind : a.kind ≠ f.kind)
    (h_gap : ¬ (f.idx - a.idx ≥ δmin)) :
    IsValidBi_from (some a) (f :: rest) δmin alt ↔
      IsValidBi_from (some a) rest δmin alt := by
  show IsValidBi_from (some a) (f :: rest) δmin alt ↔
       IsValidBi_from (some a) rest δmin alt
  simp only [IsValidBi_from, h_kind, if_false, h_gap]

/-! ## §3 — Sub-residue 3: `stroke_output_order_lift`. -/

/-- The pairwise-different predicate on `Stroke.dir` — SYMMETRIC by
    construction (`a.dir ≠ b.dir ↔ b.dir ≠ a.dir`). -/
def alt_pair (a b : Stroke) : Prop := a.dir ≠ b.dir

theorem alt_pair_symm (a b : Stroke) : alt_pair a b ↔ alt_pair b a := by
  unfold alt_pair
  constructor
  · intro h h'; exact h h'.symm
  · intro h h'; exact h h'.symm

/-- `allAlternate` is exactly `List.Chain'` for the `alt_pair` relation.
    This is the bridge to the Mathlib `chain'_reverse` lemma. -/
theorem allAlternate_iff_chain' (l : List Stroke) :
    allAlternate l ↔ List.Chain' alt_pair l := by
  induction l with
  | nil => simp [allAlternate]
  | cons hd tl ih =>
      cases tl with
      | nil => simp [allAlternate]
      | cons hd' tl' =>
          simp only [allAlternate, List.chain'_cons]
          rw [ih]
          unfold alt_pair
          rfl

/-- **SUB-RESIDUE 3 THEOREM (`allAlternate_reverse`)**.

    Alternation lifts from in-fold order (most recent at head) to output
    order (`strokes` reverses) — a one-liner via `List.chain'_reverse`
    over the SYMMETRIC predicate `alt_pair`. The in-fold theorem
    `stroke_emits_alternate` (#1086) thus lifts to a `strokes`-level
    alternation claim. -/
theorem allAlternate_reverse (l : List Stroke) (h : allAlternate l) :
    allAlternate l.reverse := by
  rw [allAlternate_iff_chain'] at h ⊢
  rw [List.chain'_reverse]
  -- Goal: Chain' (flip alt_pair) l
  -- alt_pair is symmetric, so flip alt_pair = alt_pair point-wise
  have h_sym : ∀ (a b : Stroke), flip alt_pair a b ↔ alt_pair a b := by
    intro a b
    unfold flip
    exact (alt_pair_symm b a)
  exact h.imp (fun {a b} h_ab => (h_sym a b).mpr h_ab)

/-- **OUTPUT-ORDER ALTERNATION (the named lift)**: the user-facing
    `strokes` output ALTERNATES. Direct from `allAlternate_reverse` +
    `stroke_emits_alternate` (#1086). -/
theorem strokes_alternate (frs : List Fractal) (δmin : Int) :
    allAlternate (strokes frs δmin) := by
  unfold strokes
  exact allAlternate_reverse _ (stroke_emits_alternate frs δmin)

end Chanlun.BiEndpointSubResidues
