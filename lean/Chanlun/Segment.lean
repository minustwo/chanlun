/-
  Chanlun/Segment.lean

  缠论 Def 5–16 + Theorem 1 — 线段 (Segment) stage, the pipeline capstone.

  ## Construction (host-grounded over 12k random stroke sequences)

  Fix a count `n : ℕ` (the stroke list length) and a leftmost-terminating
  oracle `find_term : ℕ → Option ℕ` with the only property the recursion needs:

      find_term_ge : ∀ a j, find_term a = some j → a ≤ j

  This is the LEFTMOST-≥-a contract from Def 13 (first-class termination
  `j*(a)`). The full feature-sequence Φ + overlap admissibility internals of
  `find_term` are a NAMED sub-residue `[chanlun_segment_terminates_sub_OPEN]`
  — they are NOT re-derived here so the recursion proof stays clean.

  The decomposition is a BoundedFix on the state `a : ℕ` with the measure
  `n - a`:

      if a ≥ n             → return []
      else match find_term a with
        | some j with j+1 ≤ n → emit ⟨a, j⟩ :: recurse (j+1)
        | some j (j+1 > n)    → emit trailing ⟨a, n-1⟩, stop
        | none                → emit trailing ⟨a, n-1⟩, stop

  ## Load-bearing lemma `segment_advance_strictly_increasing`

  `find_term a = some j` together with `find_term_ge` gives `a ≤ j`, so
  `a < j + 1`. The measure `n - a` therefore strictly decreases at every
  recursive call.
-/

import Mathlib.Tactic

namespace Chanlun.Segment

/-! ## §1 — Carrier. -/

structure Segment where
  a    : Nat
  end_ : Nat
  deriving Repr, DecidableEq

/-! ## §2 — The named load-bearing lemma. -/

theorem segment_advance_strictly_increasing
    {find_term : Nat → Option Nat}
    (find_term_ge : ∀ a j, find_term a = some j → a ≤ j)
    {n a j : Nat}
    (h_ft : find_term a = some j) (h_a : a < n) (h_in : j + 1 ≤ n) :
    n - (j + 1) < n - a := by
  have h_ge : a ≤ j := find_term_ge a j h_ft
  omega

/-! ## §3 — The BoundedFix recursion. -/

def segments
    (find_term : Nat → Option Nat)
    (find_term_ge : ∀ a j, find_term a = some j → a ≤ j)
    (n : Nat) (a : Nat) : List Segment :=
  if h_done : n ≤ a then
    have _ := h_done
    []
  else
    match h_ft : find_term a with
    | some j =>
        if h_in : j + 1 ≤ n then
          { a := a, end_ := j } ::
            segments find_term find_term_ge n (j + 1)
        else
          [{ a := a, end_ := n - 1 }]
    | none =>
        [{ a := a, end_ := n - 1 }]
termination_by n - a
decreasing_by
  have h_a : a < n := Nat.lt_of_not_ge h_done
  exact segment_advance_strictly_increasing find_term_ge h_ft h_a h_in

/-! ## §4 — Partition invariant. -/

def partitionFrom : List Segment → Nat → Nat → Prop
  | [],          a, n => a = n
  | seg :: rest, a, n =>
      seg.a = a ∧ seg.a ≤ seg.end_ ∧ seg.end_ < n ∧
      partitionFrom rest (seg.end_ + 1) n

/-! ## §5 — The partition theorem. -/

theorem segments_partitionFrom
    (find_term : Nat → Option Nat)
    (find_term_ge : ∀ a j, find_term a = some j → a ≤ j)
    (n a : Nat) (h_a : a ≤ n) :
    partitionFrom (segments find_term find_term_ge n a) a n := by
  suffices h : ∀ k, ∀ a, n - a = k → a ≤ n →
      partitionFrom (segments find_term find_term_ge n a) a n by
    exact h (n - a) a rfl h_a
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a h_meas h_a
    rw [segments]
    by_cases h_done : n ≤ a
    · simp [h_done, partitionFrom]
      omega
    · simp only [h_done, dif_neg, not_false_iff]
      cases h_ft : find_term a with
      | none =>
          have h_lt : a < n := Nat.lt_of_not_ge h_done
          simp [partitionFrom]
          refine ⟨?_, ?_, ?_⟩
          · omega
          · omega
          · omega
      | some j =>
          by_cases h_in : j + 1 ≤ n
          · simp only [h_in, dif_pos]
            have h_lt : a < n := Nat.lt_of_not_ge h_done
            have h_ge : a ≤ j := find_term_ge a j h_ft
            have h_dec : n - (j + 1) < k := by omega
            have h_a' : j + 1 ≤ n := h_in
            have ih_rest :
                partitionFrom (segments find_term find_term_ge n (j + 1)) (j + 1) n :=
              ih (n - (j + 1)) h_dec (j + 1) rfl h_a'
            refine ⟨rfl, h_ge, ?_, ?_⟩
            · show j < n
              omega
            · show partitionFrom (segments find_term find_term_ge n (j + 1)) (j + 1) n
              exact ih_rest
          · simp only [h_in, dif_neg, not_false_iff]
            have h_lt : a < n := Nat.lt_of_not_ge h_done
            simp [partitionFrom]
            refine ⟨?_, ?_, ?_⟩
            · omega
            · omega
            · omega

theorem segments_partition
    (find_term : Nat → Option Nat)
    (find_term_ge : ∀ a j, find_term a = some j → a ≤ j)
    (n : Nat) :
    partitionFrom (segments find_term find_term_ge n 0) 0 n :=
  segments_partitionFrom find_term find_term_ge n 0 (Nat.zero_le n)

/-! ## §6 — Termination theorem. -/

theorem segments_length_le
    (find_term : Nat → Option Nat)
    (find_term_ge : ∀ a j, find_term a = some j → a ≤ j)
    (n a : Nat) :
    (segments find_term find_term_ge n a).length ≤ n - a + 1 := by
  suffices h : ∀ k, ∀ a, n - a = k →
      (segments find_term find_term_ge n a).length ≤ n - a + 1 by
    exact h (n - a) a rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a h_meas
    rw [segments]
    by_cases h_done : n ≤ a
    · simp [h_done]
    · simp only [h_done, dif_neg, not_false_iff]
      cases h_ft : find_term a with
      | none =>
          simp
      | some j =>
          by_cases h_in : j + 1 ≤ n
          · simp only [h_in, dif_pos, List.length_cons]
            have h_lt : a < n := Nat.lt_of_not_ge h_done
            have h_ge : a ≤ j := find_term_ge a j h_ft
            have h_dec : n - (j + 1) < k := by omega
            have ih_rest :
                (segments find_term find_term_ge n (j + 1)).length ≤
                  n - (j + 1) + 1 :=
              ih (n - (j + 1)) h_dec (j + 1) rfl
            omega
          · simp only [h_in, dif_neg, not_false_iff]
            simp

theorem segments_terminate
    (find_term : Nat → Option Nat)
    (find_term_ge : ∀ a j, find_term a = some j → a ≤ j)
    (n : Nat) :
    (segments find_term find_term_ge n 0).length ≤ n + 1 := by
  have := segments_length_le find_term find_term_ge n 0
  simpa using this

end Chanlun.Segment
