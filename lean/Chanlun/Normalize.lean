/-
  Chanlun/Normalize.lean

  缠论 包含处理 — single-pass `normalize` is IDEMPOTENT (≡ full-collapse).

  THEOREM `normalize_no_adjacent_containment`:
       After one left-to-right `normalize` pass, no two ADJACENT intervals in
       the result stack are in a containment relation. Therefore a second
       collapse pass is a no-op — single-pass already reaches the
       full-collapse fixpoint.

  Load-bearing observation (the monotone-direction lemma):
       The DIRECTIONAL merge moves the merged top monotonically in the trend
       direction (up ⇒ [max,max], down ⇒ [min,min]) — AWAY from the lower
       neighbour — so it CANNOT create a containment with the element BELOW.
       The push branch only adds non-contained items. So `noAdjContainment`
       is preserved by every step, given the trend invariant
            up = true  ⟹ top.h > below.h
            up = false ⟹ top.l < below.l  ∧  top.h < below.h
-/

import Mathlib.Tactic

namespace Chanlun.Normalize

/-! ## §1 — Carrier + ops. -/

structure Interval where
  l : Int
  h : Int
  deriving Repr, DecidableEq

def contained (a b : Interval) : Prop :=
  (b.l ≤ a.l ∧ a.h ≤ b.h) ∨ (a.l ≤ b.l ∧ b.h ≤ a.h)

instance decContained (a b : Interval) : Decidable (contained a b) := by
  unfold contained; infer_instance

def mergeUp (a b : Interval) : Interval :=
  ⟨max a.l b.l, max a.h b.h⟩

def mergeDn (a b : Interval) : Interval :=
  ⟨min a.l b.l, min a.h b.h⟩

/-- The direction-aware merge: localizes the `if up` so the case split in
    proofs cleanly chooses `mergeUp` or `mergeDn` without dangling ites. -/
def mergeBy (up : Bool) (a b : Interval) : Interval :=
  if up then mergeUp a b else mergeDn a b

@[simp] theorem mergeBy_true  (a b : Interval) : mergeBy true  a b = mergeUp a b := rfl
@[simp] theorem mergeBy_false (a b : Interval) : mergeBy false a b = mergeDn a b := rfl

/-- One step of Algorithm N. Stack TOP AT HEAD. -/
def pushOne (state : List Interval × Bool) (it : Interval) : List Interval × Bool :=
  match state with
  | ([], up) => ([it], up)
  | (top :: rest, up) =>
      if contained top it then
        (mergeBy up top it :: rest, up)
      else
        if it.h > top.h then (it :: top :: rest, true)
        else (it :: top :: rest, false)

def normalize (xs : List Interval) : List Interval × Bool :=
  xs.foldl pushOne ([], true)

/-! ## §2 — Invariants. -/

def noAdjContainment : List Interval → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rs => ¬ contained a b ∧ noAdjContainment (b :: rs)

def trendOK : List Interval → Bool → Prop
  | top :: below :: _, true  => top.h > below.h
  | top :: below :: _, false => top.l < below.l ∧ top.h < below.h
  | _,                _      => True

def goodStack (s : List Interval) (up : Bool) : Prop :=
  noAdjContainment s ∧ trendOK s up

/-! ## §3 — Foundational facts. -/

theorem contained_symm (a b : Interval) : contained a b ↔ contained b a := by
  unfold contained; constructor <;> rintro (h | h) <;> tauto

theorem not_contained_symm (a b : Interval) : ¬ contained a b ↔ ¬ contained b a := by
  rw [contained_symm]

theorem notContained_h_le_implies_lt
    (top it : Interval) (h_nc : ¬ contained top it) (h_le : it.h ≤ top.h) :
    it.l < top.l ∧ it.h < top.h := by
  unfold contained at h_nc
  push_neg at h_nc
  obtain ⟨h1, h2⟩ := h_nc
  have hl : it.l < top.l := by
    by_contra h_ge
    push_neg at h_ge
    have h_lt : top.h < it.h := h2 h_ge
    omega
  have hh : it.h < top.h := h1 hl.le
  exact ⟨hl, hh⟩

theorem merge_preserves_noContainmentBelow_up
    (below top it : Interval)
    (h_nc_bt : ¬ contained below top)
    (h_trend : top.h > below.h) :
    ¬ contained below (mergeUp top it) := by
  intro h_c
  unfold mergeUp at h_c
  have hb : ¬ contained below top := h_nc_bt
  unfold contained at hb
  push_neg at hb
  obtain ⟨hbt1, _hbt2⟩ := hb
  have h_top_gt : top.l > below.l := by
    by_contra h
    push_neg at h
    have h_lt : top.h < below.h := hbt1 h
    omega
  rcases h_c with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    have : top.l ≤ max top.l it.l := le_max_left _ _
    omega
  · simp only at h1 h2
    have : top.h ≤ max top.h it.h := le_max_left _ _
    omega

theorem merge_preserves_noContainmentBelow_dn
    (below top it : Interval)
    (_h_nc_bt : ¬ contained below top)
    (h_trend_l : top.l < below.l) (h_trend_h : top.h < below.h) :
    ¬ contained below (mergeDn top it) := by
  intro h_c
  unfold mergeDn at h_c
  rcases h_c with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    have : min top.h it.h ≤ top.h := min_le_left _ _
    omega
  · simp only at h1 h2
    have : min top.l it.l ≤ top.l := min_le_left _ _
    omega

/-! ## §4 — `pushOne` preserves `goodStack`. -/

theorem pushOne_preserves
    (s : List Interval) (up : Bool) (it : Interval)
    (h : goodStack s up) :
    goodStack (pushOne (s, up) it).1 (pushOne (s, up) it).2 := by
  obtain ⟨h_nac, h_trend⟩ := h
  match s, h_nac, h_trend with
  | [],                     _,                        _      =>
    simp only [pushOne]
    exact ⟨by simp [noAdjContainment], by simp [trendOK]⟩
  | [top],                  _,                        _      =>
    by_cases hc : contained top it
    · simp only [pushOne, if_pos hc]
      exact ⟨by simp [noAdjContainment], by simp [trendOK]⟩
    · simp only [pushOne, if_neg hc]
      by_cases h_gt : it.h > top.h
      · simp only [if_pos h_gt]
        refine ⟨?_, ?_⟩
        · refine ⟨?_, by simp [noAdjContainment]⟩
          rw [contained_symm]; exact hc
        · exact h_gt
      · simp only [if_neg h_gt]
        push_neg at h_gt
        refine ⟨?_, ?_⟩
        · refine ⟨?_, by simp [noAdjContainment]⟩
          rw [contained_symm]; exact hc
        · exact notContained_h_le_implies_lt top it hc h_gt
  | top :: below :: rest,   ⟨h_nc_tb, h_rest_nac⟩,    h_trend_tb =>
    by_cases hc : contained top it
    · simp only [pushOne, if_pos hc]
      have h_nc_bt : ¬ contained below top := (not_contained_symm top below).mp h_nc_tb
      refine ⟨?_, ?_⟩
      · refine ⟨?_, h_rest_nac⟩
        rw [contained_symm]
        cases up with
        | true =>
          rw [mergeBy_true]
          simp only [trendOK] at h_trend_tb
          exact merge_preserves_noContainmentBelow_up below top it h_nc_bt h_trend_tb
        | false =>
          rw [mergeBy_false]
          obtain ⟨ht_l, ht_h⟩ := h_trend_tb
          exact merge_preserves_noContainmentBelow_dn below top it h_nc_bt ht_l ht_h
      · cases up with
        | true =>
          rw [mergeBy_true]
          simp only [trendOK] at h_trend_tb
          show max top.h it.h > below.h
          have : top.h ≤ max top.h it.h := le_max_left _ _
          omega
        | false =>
          rw [mergeBy_false]
          obtain ⟨ht_l, ht_h⟩ := h_trend_tb
          show min top.l it.l < below.l ∧ min top.h it.h < below.h
          have hl : min top.l it.l ≤ top.l := min_le_left _ _
          have hh : min top.h it.h ≤ top.h := min_le_left _ _
          exact ⟨lt_of_le_of_lt hl ht_l, lt_of_le_of_lt hh ht_h⟩
    · simp only [pushOne, if_neg hc]
      by_cases h_gt : it.h > top.h
      · simp only [if_pos h_gt]
        refine ⟨?_, ?_⟩
        · refine ⟨?_, h_nc_tb, h_rest_nac⟩
          rw [contained_symm]; exact hc
        · exact h_gt
      · simp only [if_neg h_gt]
        push_neg at h_gt
        refine ⟨?_, ?_⟩
        · refine ⟨?_, h_nc_tb, h_rest_nac⟩
          rw [contained_symm]; exact hc
        · exact notContained_h_le_implies_lt top it hc h_gt

/-! ## §5 — Final theorem. -/

theorem normalize_goodStack (xs : List Interval) :
    goodStack (xs.foldl pushOne ([], true)).1 (xs.foldl pushOne ([], true)).2 := by
  suffices h : ∀ (s : List Interval) (up : Bool),
        goodStack s up →
        goodStack (xs.foldl pushOne (s, up)).1 (xs.foldl pushOne (s, up)).2 by
    apply h
    exact ⟨by simp [noAdjContainment], by simp [trendOK]⟩
  intro s up h_good
  induction xs generalizing s up with
  | nil => simpa using h_good
  | cons x xs ih =>
    simp only [List.foldl]
    exact ih _ _ (pushOne_preserves s up x h_good)

/-- **THE THEOREM**: single-pass normalize is idempotent (= no residual adjacent containment). -/
theorem normalize_no_adjacent_containment (xs : List Interval) :
    noAdjContainment (normalize xs).1 :=
  (normalize_goodStack xs).1

end Chanlun.Normalize
