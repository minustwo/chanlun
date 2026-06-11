/-
  Chanlun/StrokesIsValidBiCorollary.lean

  缠论 Lemma 2 STRONG form — the NON-VACUITY corollary. Closes
  `[chanlun_bi_strokes_isValidBi_corollary_OPEN]` (Klaus dispatch on
  #1081 2026-06-11, P5 of the parallel-cc round).

  ## What this closes

  PR #1090 (`ChanlunStrokeUniquenessNFFromMSTNFMWE`) proved:

      strokes_unique :
          IsValidBi frs δmin alt → alt = strokes frs δmin

  i.e. ANY `IsValidBi`-witness IS the canonical `strokes` output —
  uniqueness. PR #1090 §3 explicitly named the non-vacuity follow-up:
  the REVERSE direction — the canonical `strokes` output is ITSELF a
  `IsValidBi`-witness. Without this, `strokes_unique` is vacuously true
  if `IsValidBi frs δmin alt` had no inhabitants.

  Together with `strokes_unique`, this MWE gives the FULL determinacy
  verdict:

      strokes_iff_IsValidBi :
          alt = strokes frs δmin ↔ IsValidBi frs δmin alt

  Lemma 2 strong: every 缠论-valid stroke decomposition IS the unique
  canonical output AND the canonical output IS a 缠论-valid decomposition.

  ## Proof strategy

  Define the canonical alt directly by recursion (mirroring `IsValidBi_from`'s
  case analysis — same case split as `step`):

      canonAlt : Option Fractal → List Fractal → Int → List Stroke

  Two lemmas:

  1. **`canonAlt_isValidBi_from`** (the structural reverse direction):
     `IsValidBi_from anchor frs δmin (canonAlt anchor frs δmin)`.
     Structural induction on `frs`; each case is a direct unfold matching
     the corresponding `IsValidBi_from` branch.

  2. **`strokes_eq_canonAlt`** (connect canonical to fold output):
     `strokes frs δmin = canonAlt none frs δmin`. Follows from PR #1090's
     `fold_consumes_alt` by instantiating `alt := canonAlt none frs δmin`
     and using `canonAlt_isValidBi_from` to discharge the premise.

  Combining (1) + (2) gives `strokes_isValidBi`. Combining
  `strokes_isValidBi` + `strokes_unique` gives `strokes_iff_IsValidBi`.

  ## Honest scope

  This is the structural reverse half — non-vacuity. The three sub-residues
  named in PR #1090 §3 (`[chanlun_bi_to_endpoint_first_admissible_OPEN]`,
  `[chanlun_bi_close_drop_named_residue_OPEN]`,
  `[chanlun_stroke_output_order_lift_OPEN]`) are orthogonal to this
  corollary and remain open.
-/

import Mathlib.Tactic
import Chanlun.Stroke
import Chanlun.StrokeUniqueness

namespace Chanlun.StrokesIsValidBiCorollary

open Chanlun.Stroke
open Chanlun.StrokeUniqueness

/-! ## §1 — The canonical alt. -/

/-- The canonical structural alt produced from a `(anchor, frs, δmin)`
    triple. Mirrors the case analysis of `IsValidBi_from` exactly:

    * `[]` → `[]`
    * no anchor → set anchor, no emit, recurse
    * same kind → `pickRep` update, no emit, recurse
    * opposite kind + gap ≥ δmin → EMIT `⟨a.idx, f.idx, emitDir f⟩`,
      re-anchor to `f`, recurse
    * opposite kind + gap < δmin → drop (state unchanged), recurse

    This is the CANONICAL output of the leftmost-greedy algorithm in
    structural-recursion form (vs `step`'s fold-state form). -/
def canonAlt : Option Fractal → List Fractal → Int → List Stroke
  | _,        [],       _    => []
  | none,     f :: rest, δmin => canonAlt (some f) rest δmin
  | some a, f :: rest, δmin =>
      if a.kind = f.kind then
        canonAlt (some (pickRep a f)) rest δmin
      else if f.idx - a.idx ≥ δmin then
        ⟨a.idx, f.idx, emitDir f⟩ :: canonAlt (some f) rest δmin
      else
        canonAlt (some a) rest δmin

/-! ## §2 — The structural lemma: `canonAlt` IS a `IsValidBi`-witness. -/

/-- THE STRUCTURAL REVERSE-DIRECTION LEMMA. The canonical alt produced
    from any `(anchor, frs, δmin)` triple satisfies `IsValidBi_from`.
    By structural induction on `frs` — each branch of `canonAlt` matches
    the corresponding `IsValidBi_from` branch exactly. -/
theorem canonAlt_isValidBi_from (δmin : Int) :
    ∀ (anchor : Option Fractal) (frs : List Fractal),
      IsValidBi_from anchor frs δmin (canonAlt anchor frs δmin) := by
  intro anchor frs
  induction frs generalizing anchor with
  | nil =>
      -- canonAlt _ [] _ = []
      -- IsValidBi_from _ [] _ alt = (alt = [])
      cases anchor <;> simp [canonAlt, IsValidBi_from]
  | cons f rest ih =>
      cases anchor with
      | none =>
          -- canonAlt none (f :: rest) δmin = canonAlt (some f) rest δmin
          -- IsValidBi_from none (f :: rest) δmin alt = IsValidBi_from (some f) rest δmin alt
          simp only [canonAlt, IsValidBi_from]
          exact ih (some f)
      | some a =>
          by_cases h_kind : a.kind = f.kind
          · -- same-kind branch
            simp only [canonAlt, IsValidBi_from, h_kind, if_true]
            exact ih (some (pickRep a f))
          · simp only [canonAlt, IsValidBi_from, h_kind, if_false]
            by_cases h_gap : f.idx - a.idx ≥ δmin
            · -- emit branch
              simp only [h_gap, if_true]
              -- Goal: ∃ rest_alt, ⟨a.idx, f.idx, emitDir f⟩ :: canonAlt (some f) rest δmin =
              --                   ⟨a.idx, f.idx, emitDir f⟩ :: rest_alt ∧
              --                   IsValidBi_from (some f) rest δmin rest_alt
              refine ⟨canonAlt (some f) rest δmin, rfl, ?_⟩
              exact ih (some f)
            · -- drop branch
              simp only [h_gap, if_false]
              exact ih (some a)

/-! ## §3 — Connecting `canonAlt` to the streaming `strokes`. -/

/-- The canonical alt at `anchor = none` equals the user-facing `strokes`
    output. Direct consequence of PR #1090's `fold_consumes_alt`
    instantiated at `alt := canonAlt none frs δmin` (the premise is
    discharged by `canonAlt_isValidBi_from`).

    `fold_consumes_alt` gives `(fold _).out = alt.reverse ++ out₀`.
    With `out₀ = []` and `alt = canonAlt none frs δmin`:
    `(fold _ ⟨none, []⟩).out = (canonAlt none frs δmin).reverse`. Reversing
    both sides and noting `strokes frs δmin = (fold _).out.reverse` gives
    the result. -/
theorem strokes_eq_canonAlt (frs : List Fractal) (δmin : Int) :
    strokes frs δmin = canonAlt none frs δmin := by
  have h_iv : IsValidBi_from none frs δmin (canonAlt none frs δmin) :=
    canonAlt_isValidBi_from δmin none frs
  have h_fold := fold_consumes_alt δmin frs none [] (canonAlt none frs δmin) h_iv
  -- h_fold : (frs.foldl (step δmin) ⟨none, []⟩).out = (canonAlt none frs δmin).reverse ++ []
  have h_empty : (StrokeState.empty : StrokeState) = ⟨none, []⟩ := rfl
  rw [← h_empty] at h_fold
  simp at h_fold
  -- h_fold : (frs.foldl (step δmin) StrokeState.empty).out = (canonAlt none frs δmin).reverse
  unfold strokes
  rw [h_fold]
  exact List.reverse_reverse _

/-! ## §4 — THE NON-VACUITY THEOREM (Klaus's named P5 target). -/

/-- **THE NON-VACUITY THEOREM** (Klaus's named P5 target). The canonical
    streaming output `strokes frs δmin` IS itself a `IsValidBi`-witness.
    Together with `strokes_unique` (PR #1090), this gives the
    `IsValidBi ↔ canonical` biconditional below — confirming
    `strokes_unique` is non-vacuous. -/
theorem strokes_isValidBi (frs : List Fractal) (δmin : Int) :
    IsValidBi frs δmin (strokes frs δmin) := by
  unfold IsValidBi
  rw [strokes_eq_canonAlt]
  exact canonAlt_isValidBi_from δmin none frs

/-! ## §5 — THE FULL DETERMINACY VERDICT. -/

/-- **THE FULL DETERMINACY VERDICT** (Klaus's named P5 second target).
    Bidirectional: `alt` is a valid 缠论-Lemma-2 decomposition IFF it
    equals the canonical streaming output. Combines `strokes_unique`
    (PR #1090, forward) with `strokes_isValidBi` (this MWE, reverse). -/
theorem strokes_iff_IsValidBi
    (frs : List Fractal) (δmin : Int) (alt : List Stroke) :
    alt = strokes frs δmin ↔ IsValidBi frs δmin alt := by
  constructor
  · intro h_eq
    rw [h_eq]
    exact strokes_isValidBi frs δmin
  · intro h_iv
    exact strokes_unique frs δmin alt h_iv

end Chanlun.StrokesIsValidBiCorollary
