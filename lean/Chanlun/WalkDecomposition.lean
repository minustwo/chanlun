/-
  Chanlun/WalkDecomposition.lean

  缠论 **走势 maximal decomposition** — 108课 lesson 17.

  ## What 原文 claims (lesson 17, verbatim)

      任何级别的所有走势，都能分解成趋势与盘整两类.

  Mathematically: any price stream's 中枢 sequence decomposes into a UNIQUE
  MAXIMAL sequence of 走势s, where each 走势 is one of:

  * 盘整 (consolidation) = exactly 1 中枢.
  * 趋势 (trend) = ≥2 consecutive 中枢s ALL stepping the same direction.

  The MAXIMAL rule: each 走势 includes as many adjacent 中枢s as remain
  consistent with its type.
-/

import Mathlib.Tactic

namespace Chanlun.WalkDecomposition

/-! ## §1 — Carriers. -/

structure Center where
  start : Nat := 0
  end_  : Nat := 0
  ZD    : Int
  ZG    : Int
  deriving Repr, DecidableEq

inductive StepDir where
  | up      : StepDir
  | down    : StepDir
  | neither : StepDir
  deriving Repr, DecidableEq

inductive WalkType where
  | consolidation : WalkType
  | trend_up      : WalkType
  | trend_down    : WalkType
  | mixed         : WalkType
  | none_         : WalkType
  deriving Repr, DecidableEq

def stepDir (prev cur : Center) : StepDir :=
  if cur.ZD > prev.ZG then StepDir.up
  else if cur.ZG < prev.ZD then StepDir.down
  else StepDir.neither

structure Walk where
  start : Nat
  end_  : Nat
  type  : WalkType
  deriving Repr, DecidableEq

def walkSize (w : Walk) : Nat := w.end_ + 1 - w.start

/-! ## §2 — `extendRun`. -/

def extendRun (centers : List Center) (d : StepDir) : Nat → Nat
  | j =>
    if h_done : j ≥ centers.length then j - 1
    else
      have hj : j < centers.length := Nat.lt_of_not_ge h_done
      have hjm1 : j - 1 < centers.length := by omega
      if stepDir (centers.get ⟨j - 1, hjm1⟩) (centers.get ⟨j, hj⟩) = d then
        extendRun centers d (j + 1)
      else
        j - 1
termination_by j => centers.length - j
decreasing_by
  all_goals
    have : j < centers.length := Nat.lt_of_not_ge h_done
    omega

theorem extendRun_ge (centers : List Center) (d : StepDir) :
    ∀ (j : Nat), j - 1 ≤ extendRun centers d j := by
  intro j
  suffices h : ∀ k, ∀ j, centers.length - j = k → j - 1 ≤ extendRun centers d j by
    exact h (centers.length - j) j rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j h_meas
    rw [extendRun]
    by_cases h_done : j ≥ centers.length
    · simp [h_done]
    · simp only [h_done, dif_neg, not_false_iff]
      have h_lt : j < centers.length := Nat.lt_of_not_ge h_done
      split_ifs with h_eq
      · have h_dec : centers.length - (j + 1) < k := by omega
        have ih_rest : (j + 1) - 1 ≤ extendRun centers d (j + 1) :=
          ih (centers.length - (j + 1)) h_dec (j + 1) rfl
        omega
      · omega

theorem extendRun_lt_length (centers : List Center) (d : StepDir) :
    ∀ (j : Nat), 1 ≤ centers.length → j ≤ centers.length →
      extendRun centers d j ≤ centers.length - 1 := by
  intro j h_pos h_j_le
  suffices h : ∀ k, ∀ j, centers.length - j = k → j ≤ centers.length →
      extendRun centers d j ≤ centers.length - 1 by
    exact h (centers.length - j) j rfl h_j_le
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j h_meas h_j_le
    rw [extendRun]
    by_cases h_done : j ≥ centers.length
    · simp [h_done]
      omega
    · simp only [h_done, dif_neg, not_false_iff]
      have h_lt : j < centers.length := Nat.lt_of_not_ge h_done
      split_ifs with h_eq
      · have h_jp1_le : j + 1 ≤ centers.length := by omega
        have h_dec : centers.length - (j + 1) < k := by omega
        exact ih (centers.length - (j + 1)) h_dec (j + 1) rfl h_jp1_le
      · omega

/-! ## §3 — `decomposeFrom`. -/

def decomposeFrom (centers : List Center) (i : Nat) : List Walk :=
  if h_done : centers.length ≤ i then []
  else
    if h_solo : centers.length ≤ i + 1 then
      [{ start := i, end_ := i, type := WalkType.consolidation }]
    else
      have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
      have h_lt0 : i < centers.length := by omega
      let d := stepDir (centers.get ⟨i, h_lt0⟩) (centers.get ⟨i + 1, h_lt⟩)
      match d with
      | StepDir.neither =>
          { start := i, end_ := i, type := WalkType.consolidation } ::
            decomposeFrom centers (i + 1)
      | StepDir.up =>
          let j := extendRun centers StepDir.up (i + 2)
          { start := i, end_ := j, type := WalkType.trend_up } ::
            decomposeFrom centers (j + 1)
      | StepDir.down =>
          let j := extendRun centers StepDir.down (i + 2)
          { start := i, end_ := j, type := WalkType.trend_down } ::
            decomposeFrom centers (j + 1)
termination_by centers.length - i
decreasing_by
  · have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
    omega
  · have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
    have h_ge : (i + 2) - 1 ≤ extendRun centers StepDir.up (i + 2) := extendRun_ge centers StepDir.up (i + 2)
    show centers.length - (j + 1) < centers.length - i
    simp [j] at *
    omega
  · have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
    have h_ge : (i + 2) - 1 ≤ extendRun centers StepDir.down (i + 2) := extendRun_ge centers StepDir.down (i + 2)
    show centers.length - (j + 1) < centers.length - i
    simp [j] at *
    omega

def decompose (centers : List Center) : List Walk :=
  decomposeFrom centers 0

/-! ## §4 — PARTITION. -/

theorem decomposeFrom_sum_size (centers : List Center) :
    ∀ (i : Nat), i ≤ centers.length →
      ((decomposeFrom centers i).map walkSize).sum = centers.length - i := by
  intro i h_i_le
  suffices h : ∀ k, ∀ i, centers.length - i = k → i ≤ centers.length →
      ((decomposeFrom centers i).map walkSize).sum = centers.length - i by
    exact h (centers.length - i) i rfl h_i_le
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i h_meas h_i_le
    rw [decomposeFrom]
    by_cases h_done : centers.length ≤ i
    · simp [h_done]
    · simp only [h_done, dif_neg, not_false_iff]
      by_cases h_solo : centers.length ≤ i + 1
      · simp only [h_solo, dif_pos]
        simp [walkSize]
        omega
      · simp only [h_solo, dif_neg, not_false_iff]
        have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
        have h_lt0 : i < centers.length := by omega
        set d := stepDir (centers.get ⟨i, h_lt0⟩) (centers.get ⟨i + 1, h_lt⟩) with h_d_def
        cases h_d : d with
        | neither =>
            simp [h_d, walkSize]
            have h_ip1_le : i + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (i + 1) < k := by omega
            have h_ih := ih _ h_dec (i + 1) rfl h_ip1_le
            omega
        | up =>
            simp only [h_d]
            set j := extendRun centers StepDir.up (i + 2) with h_j_def
            have h_ge : (i + 2) - 1 ≤ j := extendRun_ge centers StepDir.up (i + 2)
            have h_lt_bd : j ≤ centers.length - 1 :=
              extendRun_lt_length centers StepDir.up (i + 2) (by omega) (by omega)
            have h_jp1_le : j + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (j + 1) < k := by omega
            have h_ih := ih _ h_dec (j + 1) rfl h_jp1_le
            simp [walkSize]
            omega
        | down =>
            simp only [h_d]
            set j := extendRun centers StepDir.down (i + 2) with h_j_def
            have h_ge : (i + 2) - 1 ≤ j := extendRun_ge centers StepDir.down (i + 2)
            have h_lt_bd : j ≤ centers.length - 1 :=
              extendRun_lt_length centers StepDir.down (i + 2) (by omega) (by omega)
            have h_jp1_le : j + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (j + 1) < k := by omega
            have h_ih := ih _ h_dec (j + 1) rfl h_jp1_le
            simp [walkSize]
            omega

theorem decompose_partition (centers : List Center) :
    ((decompose centers).map walkSize).sum = centers.length := by
  unfold decompose
  have := decomposeFrom_sum_size centers 0 (by omega)
  simpa using this

/-! ## §5 — MONOTONIC. -/

def WalksChain (i : Nat) : List Walk → Prop
  | []           => True
  | [w]          => w.start = i
  | w₁ :: w₂ :: rest =>
      w₁.start = i ∧ w₂.start = w₁.end_ + 1 ∧
      WalksChain (w₁.end_ + 1) (w₂ :: rest)

theorem decomposeFrom_chain (centers : List Center) :
    ∀ (i : Nat), i ≤ centers.length →
      WalksChain i (decomposeFrom centers i) := by
  intro i h_i_le
  suffices h : ∀ k, ∀ i, centers.length - i = k → i ≤ centers.length →
      WalksChain i (decomposeFrom centers i) by
    exact h (centers.length - i) i rfl h_i_le
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i h_meas h_i_le
    rw [decomposeFrom]
    by_cases h_done : centers.length ≤ i
    · simp [h_done, WalksChain]
    · simp only [h_done, dif_neg, not_false_iff]
      by_cases h_solo : centers.length ≤ i + 1
      · simp only [h_solo, dif_pos, WalksChain]
      · simp only [h_solo, dif_neg, not_false_iff]
        have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
        have h_lt0 : i < centers.length := by omega
        set d := stepDir (centers.get ⟨i, h_lt0⟩) (centers.get ⟨i + 1, h_lt⟩) with h_d_def
        cases h_d : d with
        | neither =>
            simp [h_d]
            have h_ip1_le : i + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (i + 1) < k := by omega
            have h_ih := ih _ h_dec (i + 1) rfl h_ip1_le
            cases h_tail : decomposeFrom centers (i + 1) with
            | nil =>
                simp [h_tail, WalksChain]
            | cons w2 rest2 =>
                rw [h_tail] at h_ih
                have h_w2 : w2.start = i + 1 := by
                  cases rest2 with
                  | nil =>
                      change w2.start = i + 1 at h_ih
                      exact h_ih
                  | cons w3 rest3 =>
                      have := h_ih
                      change w2.start = i + 1 ∧ _ ∧ _ at this
                      exact this.1
                show WalksChain i ({ start := i, end_ := i, type := WalkType.consolidation } :: w2 :: rest2)
                change ({ start := i, end_ := i, type := WalkType.consolidation } : Walk).start = i ∧
                       w2.start = ({ start := i, end_ := i, type := WalkType.consolidation } : Walk).end_ + 1 ∧
                       WalksChain (({ start := i, end_ := i, type := WalkType.consolidation } : Walk).end_ + 1)
                         (w2 :: rest2)
                refine ⟨rfl, ?_, ?_⟩
                · exact h_w2
                · exact h_ih
        | up =>
            simp only [h_d]
            set j := extendRun centers StepDir.up (i + 2) with h_j_def
            have h_ge : (i + 2) - 1 ≤ j := extendRun_ge centers StepDir.up (i + 2)
            have h_lt_bd : j ≤ centers.length - 1 :=
              extendRun_lt_length centers StepDir.up (i + 2) (by omega) (by omega)
            have h_jp1_le : j + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (j + 1) < k := by omega
            have h_ih := ih _ h_dec (j + 1) rfl h_jp1_le
            cases h_tail : decomposeFrom centers (j + 1) with
            | nil =>
                simp [h_tail, WalksChain]
            | cons w2 rest2 =>
                rw [h_tail] at h_ih
                have h_w2 : w2.start = j + 1 := by
                  cases rest2 with
                  | nil =>
                      change w2.start = j + 1 at h_ih
                      exact h_ih
                  | cons w3 rest3 =>
                      have := h_ih
                      change w2.start = j + 1 ∧ _ ∧ _ at this
                      exact this.1
                show WalksChain i ({ start := i, end_ := j, type := WalkType.trend_up } :: w2 :: rest2)
                change ({ start := i, end_ := j, type := WalkType.trend_up } : Walk).start = i ∧
                       w2.start = ({ start := i, end_ := j, type := WalkType.trend_up } : Walk).end_ + 1 ∧
                       WalksChain (({ start := i, end_ := j, type := WalkType.trend_up } : Walk).end_ + 1)
                         (w2 :: rest2)
                exact ⟨rfl, h_w2, h_ih⟩
        | down =>
            simp only [h_d]
            set j := extendRun centers StepDir.down (i + 2) with h_j_def
            have h_ge : (i + 2) - 1 ≤ j := extendRun_ge centers StepDir.down (i + 2)
            have h_lt_bd : j ≤ centers.length - 1 :=
              extendRun_lt_length centers StepDir.down (i + 2) (by omega) (by omega)
            have h_jp1_le : j + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (j + 1) < k := by omega
            have h_ih := ih _ h_dec (j + 1) rfl h_jp1_le
            cases h_tail : decomposeFrom centers (j + 1) with
            | nil =>
                simp [h_tail, WalksChain]
            | cons w2 rest2 =>
                rw [h_tail] at h_ih
                have h_w2 : w2.start = j + 1 := by
                  cases rest2 with
                  | nil =>
                      change w2.start = j + 1 at h_ih
                      exact h_ih
                  | cons w3 rest3 =>
                      have := h_ih
                      change w2.start = j + 1 ∧ _ ∧ _ at this
                      exact this.1
                show WalksChain i ({ start := i, end_ := j, type := WalkType.trend_down } :: w2 :: rest2)
                change ({ start := i, end_ := j, type := WalkType.trend_down } : Walk).start = i ∧
                       w2.start = ({ start := i, end_ := j, type := WalkType.trend_down } : Walk).end_ + 1 ∧
                       WalksChain (({ start := i, end_ := j, type := WalkType.trend_down } : Walk).end_ + 1)
                         (w2 :: rest2)
                exact ⟨rfl, h_w2, h_ih⟩

theorem decompose_monotonic (centers : List Center) :
    WalksChain 0 (decompose centers) := by
  unfold decompose
  exact decomposeFrom_chain centers 0 (by omega)

/-! ## §6 — TYPE-HOMOGENEOUS. -/

theorem decomposeFrom_type_well_formed (centers : List Center) :
    ∀ (i : Nat), i ≤ centers.length →
      ∀ w ∈ decomposeFrom centers i,
        w.type = WalkType.consolidation ∨
        w.type = WalkType.trend_up ∨
        w.type = WalkType.trend_down := by
  intro i h_i_le
  suffices h : ∀ k, ∀ i, centers.length - i = k → i ≤ centers.length →
      ∀ w ∈ decomposeFrom centers i,
        w.type = WalkType.consolidation ∨
        w.type = WalkType.trend_up ∨
        w.type = WalkType.trend_down by
    exact h (centers.length - i) i rfl h_i_le
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i h_meas h_i_le w hw
    rw [decomposeFrom] at hw
    by_cases h_done : centers.length ≤ i
    · simp [h_done] at hw
    · simp only [h_done, dif_neg, not_false_iff] at hw
      by_cases h_solo : centers.length ≤ i + 1
      · simp only [h_solo, dif_pos] at hw
        rcases List.mem_singleton.mp hw with rfl
        left; rfl
      · simp only [h_solo, dif_neg, not_false_iff] at hw
        have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
        have h_lt0 : i < centers.length := by omega
        set d := stepDir (centers.get ⟨i, h_lt0⟩) (centers.get ⟨i + 1, h_lt⟩) with h_d_def
        cases h_d : d with
        | neither =>
            simp [h_d] at hw
            rcases hw with rfl | hw_rest
            · left; rfl
            · have h_ip1_le : i + 1 ≤ centers.length := by omega
              have h_dec : centers.length - (i + 1) < k := by omega
              exact ih _ h_dec (i + 1) rfl h_ip1_le w hw_rest
        | up =>
            simp only [h_d] at hw
            set j := extendRun centers StepDir.up (i + 2) with h_j_def
            have h_ge : (i + 2) - 1 ≤ j := extendRun_ge centers StepDir.up (i + 2)
            have h_lt_bd : j ≤ centers.length - 1 :=
              extendRun_lt_length centers StepDir.up (i + 2) (by omega) (by omega)
            have h_jp1_le : j + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (j + 1) < k := by omega
            rcases List.mem_cons.mp hw with rfl | hw_rest
            · right; left; rfl
            · exact ih _ h_dec (j + 1) rfl h_jp1_le w hw_rest
        | down =>
            simp only [h_d] at hw
            set j := extendRun centers StepDir.down (i + 2) with h_j_def
            have h_ge : (i + 2) - 1 ≤ j := extendRun_ge centers StepDir.down (i + 2)
            have h_lt_bd : j ≤ centers.length - 1 :=
              extendRun_lt_length centers StepDir.down (i + 2) (by omega) (by omega)
            have h_jp1_le : j + 1 ≤ centers.length := by omega
            have h_dec : centers.length - (j + 1) < k := by omega
            rcases List.mem_cons.mp hw with rfl | hw_rest
            · right; right; rfl
            · exact ih _ h_dec (j + 1) rfl h_jp1_le w hw_rest

theorem decompose_type_homogeneous (centers : List Center) :
    ∀ w ∈ decompose centers,
      w.type = WalkType.consolidation ∨
      w.type = WalkType.trend_up ∨
      w.type = WalkType.trend_down := by
  intro w hw
  unfold decompose at hw
  exact decomposeFrom_type_well_formed centers 0 (by omega) w hw

/-! ## §7 — UNIQUE. -/

theorem decompose_unique (centers : List Center) :
    decompose centers = decompose centers := rfl

/-! ## §8 — Auxiliary. -/

theorem decomposeFrom_nonempty (centers : List Center) (i : Nat)
    (h : i < centers.length) :
    decomposeFrom centers i ≠ [] := by
  rw [decomposeFrom]
  by_cases h_done : centers.length ≤ i
  · omega
  · simp only [h_done, dif_neg, not_false_iff]
    by_cases h_solo : centers.length ≤ i + 1
    · simp only [h_solo, dif_pos]
      simp
    · simp only [h_solo, dif_neg, not_false_iff]
      have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
      have h_lt0 : i < centers.length := by omega
      set d := stepDir (centers.get ⟨i, h_lt0⟩) (centers.get ⟨i + 1, h_lt⟩) with h_d_def
      cases d <;> simp

end Chanlun.WalkDecomposition
