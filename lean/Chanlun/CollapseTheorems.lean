/-
  Chanlun/CollapseTheorems.lean

  缠论 multi-valued residue COLLAPSE THEOREMS — Klaus's classification of
  the 6 MULTI_VALUED_NAMED items into:

    * Class A — collapsible under a data-side condition. Two readings
      agree whenever the input has property P. New data CAN settle the
      ambiguity by satisfying P.
    * Class B — semantically multi-valued. The choice is an oracle /
      measure choice that the master text leaves open. New data CANNOT
      decide between readings; the gate is structurally relative.

  This module discharges the Class A collapse theorems for the two §X.5
  zone-gate items that did not previously have a collapse theorem.

  ## What this module proves

  * `zhongshu_zone_gate_collapses_when_no_tightening` — on element
    sequences where every post-first-3 admitted element CONTAINS the
    first3 zone (`e.lo ≤ zd ∧ e.hi ≥ zg`), the `first3` and `all_`
    readings of `extendEnd` return the same end index.

  * `zhongshu_shoulder_collapses_off_boundary` — on element sequences
    where every post-first-3 element is OFF the zone boundary
    (`e.lo ≠ zg ∧ e.hi ≠ zd`), the `≤` and strict `<` shoulder readings
    of the overlap predicate coincide.

  ## What this does NOT touch

  * X.7.5 / X.7.8 / X.8.3 — the disp-vs-slope measure gate is CLASS B
    (semantic measure choice; not collapsible by input data). The
    constructive divergence witness in `Chanlun.DivergenceWitnesses`
    stays as-is — that IS the certificate that no collapse exists.
  * X.3.7 — already has a collapse theorem in
    `Chanlun.BiEndpointSubResidues.to_endpoint_leftmost_eq_extremal_on_reachable`.
-/

import Mathlib.Tactic
import Chanlun.Zhongshu

namespace Chanlun.CollapseTheorems

open Chanlun.Zhongshu

/-! ## §1 — Zone-gate Class-A collapse (X.5.10).

    The two `extendEnd` readings agree on element sequences where every
    admitted post-first-3 element CONTAINS the first3 zone — equivalently,
    the `all_` tightening step is a no-op on each admitted element.

    This is the formal content of the chanlun.md claim "on the reachable
    (containment-free) domain the two readings coincide": when no
    admitted element strictly tightens the zone, `max zd e.lo = zd` and
    `min zg e.hi = zg`, so the `all_` recursion's tightened arguments
    are identical to the `first3` ones at every step. -/

/-- The collapse condition for `extendEnd` from index `j` against zone
    `(zd, zg)`: every element from index `j` onwards CONTAINS the zone.
    Under this condition, the `all_` tightening at each step is a no-op,
    so the `all_` and `first3` recursions stay in lockstep. -/
def ContainsZoneFrom (els : List Element) (zd zg : Int) (j : Nat) : Prop :=
  ∀ k, j ≤ k → k < els.length →
    (els.get ⟨k, by omega⟩).lo ≤ zd ∧ (els.get ⟨k, by omega⟩).hi ≥ zg

/-- **THEOREM (ZONE-GATE COLLAPSE, X.5.10, CLASS A)**.

    On element sequences where every post-`j` element CONTAINS the zone
    `(zd, zg)`, the `first3` and `all_` gates produce the SAME extended
    end index. This is the collapse theorem for the X.5.10 multi-valued
    residue: the divergence witnessed by
    `Chanlun.DivergenceWitnesses.zhongshu_zone_gate_divergence_witness`
    requires at least one admitted element that STRICTLY tightens the
    zone. On inputs where no admitted element tightens (the "wide-zone"
    reachable shape), the two readings COINCIDE.

    Form:
        ContainsZoneFrom els zd zg j →
          extendEnd els ZoneGate.first3 zd zg j =
          extendEnd els ZoneGate.all_   zd zg j. -/
theorem zhongshu_zone_gate_collapses_when_no_tightening
    (els : List Element) :
    ∀ (zd zg : Int) (j : Nat),
      ContainsZoneFrom els zd zg j →
      extendEnd els ZoneGate.first3 zd zg j =
        extendEnd els ZoneGate.all_ zd zg j := by
  intro zd zg j h_contains
  suffices h : ∀ k, ∀ zd zg j, els.length - j = k →
      ContainsZoneFrom els zd zg j →
      extendEnd els ZoneGate.first3 zd zg j =
        extendEnd els ZoneGate.all_ zd zg j by
    exact h (els.length - j) zd zg j rfl h_contains
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro zd zg j h_meas h_contains
    -- Unfold both sides — mirroring the `extendEnd_ge` proof in Zhongshu.lean.
    rw [extendEnd]
    conv_rhs => rw [extendEnd]
    by_cases h_done : j ≥ els.length
    · -- Terminal case.
      simp [h_done]
    · have h_lt : j < els.length := Nat.lt_of_not_ge h_done
      by_cases h_overlap : (els.get ⟨j, h_lt⟩).lo ≤ zg ∧ (els.get ⟨j, h_lt⟩).hi ≥ zd
      · -- Overlap admitted on both sides; gate-specific branches diverge.
        have h_contains_j :
            (els.get ⟨j, h_lt⟩).lo ≤ zd ∧ (els.get ⟨j, h_lt⟩).hi ≥ zg :=
          h_contains j (Nat.le_refl _) h_lt
        have h_max : max zd (els.get ⟨j, h_lt⟩).lo = zd :=
          max_eq_left h_contains_j.1
        have h_min : min zg (els.get ⟨j, h_lt⟩).hi = zg :=
          min_eq_left h_contains_j.2
        have h_dec : els.length - (j + 1) < k := by omega
        have h_contains_next : ContainsZoneFrom els zd zg (j + 1) := by
          intro k' h_ge h_lt'
          exact h_contains k' (by omega) h_lt'
        have ih_eq :
            extendEnd els ZoneGate.first3 zd zg (j + 1) =
              extendEnd els ZoneGate.all_ zd zg (j + 1) :=
          ih (els.length - (j + 1)) h_dec zd zg (j + 1) rfl h_contains_next
        -- Reduce the dif on both sides to the recursive call.
        simp only [h_done, dif_neg, not_false_iff, h_overlap, dif_pos]
        -- Goal is now:
        --   extendEnd els ZoneGate.first3 zd zg (j+1)
        --     = extendEnd els ZoneGate.all_
        --         (max zd (els.get ⟨j, h_lt⟩).lo)
        --         (min zg (els.get ⟨j, h_lt⟩).hi) (j+1)
        rw [h_max, h_min, ih_eq]
      · -- No overlap on either side.
        simp [h_done, h_overlap]

/-! ## §2 — Shoulder ≤ vs < Class-A collapse (X.5.11).

    The overlap predicate uses `≤` (the canonical reading). A sibling
    reading uses strict `<`. The two coincide on inputs where no
    post-first-3 element sits EXACTLY on the zone boundary (i.e.
    `e.lo = zg` or `e.hi = zd`).

    This is a pure logical collapse: when neither equality holds, the
    `≤` and `<` truth values are the same. The witness for X.5.11
    therefore requires an element that sits exactly on the shoulder. -/

/-- The shoulder ≤ reading of the overlap predicate. Matches the
    `extendEnd` implementation in `Chanlun.Zhongshu`. -/
def overlapsLE (zd zg : Int) (e : Element) : Prop :=
  e.lo ≤ zg ∧ e.hi ≥ zd

/-- The shoulder strict-< reading of the overlap predicate (the sibling
    oracle named at X.5.11). -/
def overlapsLT (zd zg : Int) (e : Element) : Prop :=
  e.lo < zg ∧ e.hi > zd

/-- The collapse condition: the element is OFF the shoulder boundary —
    neither `e.lo = zg` nor `e.hi = zd` holds. -/
def OffShoulder (zd zg : Int) (e : Element) : Prop :=
  e.lo ≠ zg ∧ e.hi ≠ zd

/-- **THEOREM (SHOULDER COLLAPSE, X.5.11, CLASS A)**.

    For any element OFF the shoulder boundary, the `≤` and strict `<`
    readings of the overlap predicate AGREE. The X.5.11 multi-valued
    residue is genuinely silent only when an element sits exactly on
    `e.lo = zg` or `e.hi = zd`. On any input where every post-first-3
    element is off-boundary, the canonical (≤) and sibling (<) oracles
    produce IDENTICAL extension decisions.

    Form:
        OffShoulder zd zg e → (overlapsLE zd zg e ↔ overlapsLT zd zg e). -/
theorem zhongshu_shoulder_collapses_off_boundary
    (zd zg : Int) (e : Element)
    (h_off : OffShoulder zd zg e) :
    overlapsLE zd zg e ↔ overlapsLT zd zg e := by
  unfold OffShoulder at h_off
  unfold overlapsLE overlapsLT
  obtain ⟨h_lo_ne, h_hi_ne⟩ := h_off
  constructor
  · intro ⟨h_lo_le, h_hi_ge⟩
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne h_lo_le h_lo_ne
    · exact lt_of_le_of_ne h_hi_ge (Ne.symm h_hi_ne)
  · intro ⟨h_lo_lt, h_hi_gt⟩
    exact ⟨le_of_lt h_lo_lt, le_of_lt h_hi_gt⟩

/-- **THEOREM (SHOULDER COLLAPSE, LIFTED TO A SEQUENCE)**.

    Lift to a full element list: if every element from index `j`
    onwards is off the shoulder boundary, the two overlap predicates
    agree pointwise on the sequence. -/
theorem zhongshu_shoulder_collapses_off_boundary_list
    (els : List Element) (zd zg : Int) (j : Nat)
    (h_off : ∀ k, j ≤ k → k < els.length →
      OffShoulder zd zg (els.get ⟨k, by omega⟩)) :
    ∀ k, j ≤ k → ∀ (h_lt : k < els.length),
      overlapsLE zd zg (els.get ⟨k, h_lt⟩) ↔
      overlapsLT zd zg (els.get ⟨k, h_lt⟩) := by
  intro k h_ge h_lt
  exact zhongshu_shoulder_collapses_off_boundary zd zg _ (h_off k h_ge h_lt)

end Chanlun.CollapseTheorems
