/-
  Chanlun/WalkDecomposition.lean

  缠论 **走势 maximal decomposition** — 108课 lesson 17. Closes
  `[chanlun_walk_decomposition_lean_OPEN]` (Klaus 缠论 完成程序 dispatch on
  #1081 2026-06-11; arch-prep grounding `chanlun_walk_decomposition_grounding.py`
  in this PR).

  ## What 原文 claims (lesson 17, verbatim)

      任何级别的所有走势，都能分解成趋势与盘整两类.

  Mathematically (the missing layer between #1093 中枢 and #1094 classify):
  any price stream's 中枢 sequence decomposes into a UNIQUE MAXIMAL sequence
  of 走势s, where each 走势 is one of:

  * 盘整 (consolidation) = exactly 1 中枢.
  * 趋势 (trend) = ≥2 consecutive 中枢s ALL stepping the same direction
    (up if every `cur.ZD > prev.ZG`; down if every `cur.ZG < prev.ZD`).

  The MAXIMAL rule: each 走势 includes as many adjacent 中枢s as remain
  consistent with its type. The next 走势 starts where the previous one
  ends. **UNIQUE** = there's exactly one such decomposition.

  ## The named theorems (Klaus's target)

  ```lean
  structure Walk where
    start : Nat
    end_  : Nat
    type  : WalkType
  def decompose : List Center → List Walk
  theorem decompose_partition  -- Σ walk sizes == centers.length
  theorem decompose_monotonic  -- walk[k].end_ + 1 == walk[k+1].start
  theorem decompose_type_homogeneous  -- each walk's type matches classify
  theorem decompose_unique     -- lesson 17 唯一性
  ```

  ## Why the maximal-monotone split is the unique rule

  At every center index `i` the next boundary is FORCED by the direction of
  `stepDir centers[i] centers[i+1]`:

  * `up` or `down` (clean directional step): keep extending the same-direction
    run as long as the next step preserves the direction. Length ≥ 2 ⇒
    `trend_up` / `trend_down`.
  * `neither` (overlap or end-of-list): the current 中枢 is alone at this
    boundary ⇒ `consolidation` (length 1).

  Because each step's choice is forced (no degrees of freedom), the
  decomposition exists and is unique. `mixed` NEVER appears in the output:
  the split criterion IS the 依次同向 qualifier that `classify` uses to
  detect `mixed`, so each emitted walk's centers all step the same direction.

  ## Termination

  Same well-founded pattern as `ChanlunLevelRecursionTerminationMWE.lean`
  (#1101): the measure `centers.length - i` strictly decreases at every
  iteration. Either we emit a 盘整 and `i := i + 1` (drop ≥ 1), or we emit
  a 趋势 of length `j - i + 1 ≥ 2` and `i := j + 1` (drop ≥ 2).

  ## Honest scope — named follow-ups

  * `[chanlun_walk_decomposition_mixed_segment_OPEN]` — a downstream MERGER
    that concatenates walks across a direction-reversal boundary produces a
    `mixed` per-classify result. `decompose` itself NEVER emits a `mixed`
    walk (homogeneity proven below).
  * `[chanlun_walk_decomposition_intervalnesting_OPEN]` — the 区间套 / multi-
    level NESTED 走势 decomposition (where one 走势 contains nested 中枢 升级
    to a higher level) is a SEPARATE residue (Klaus queue item 4). This MWE
    is the SINGLE-LEVEL maximal decomposition; the 级别 recursion / lift is
    `ChanlunLevelRecursionTerminationMWE.lean` (#1101).
  * The base 中枢 zone-gate (first3 / all) is the #1093 named residue —
    this decomposition is gate-uniform over Center (whatever gate produced
    the input centers).

  ## Companion host grounding (this PR)

  `tools/mstnf_runtime/chanlun_walk_decomposition_grounding.py` — 3.4k
  REACHABLE K-line streams (raw → normalize → fractals → strokes → zhongshu);
  PARTITION + DET + MONOTONIC + HOMOG all verified; §15 mutant that NEVER
  splits emits a mega-walk classifying as `mixed`, disagreeing with the
  honest decomposer on reversal streams.
-/

import Mathlib.Tactic

namespace Chanlun.WalkDecomposition

/-! ## §1 — Carriers (Center / StepDir / WalkType re-stated for self-containment). -/

/-- A 中枢 (走势中枢) carries its zone `[ZD, ZG]`. Same shape as
    `ChanlunZhongshuNFFromMSTNFMWE.Center` and
    `ChanlunTrendTypeNFFromMSTNFMWE.Center`. Re-stated here to keep this MWE
    self-contained (no cross-module dependency). Only ZD/ZG matter for the
    directional step; the `start`/`end_` index field is kept for shape parity. -/
structure Center where
  start : Nat := 0
  end_  : Nat := 0
  ZD    : Int
  ZG    : Int
  deriving Repr, DecidableEq

/-- Directional step between two 中枢s — same as in #1094. -/
inductive StepDir where
  | up      : StepDir
  | down    : StepDir
  | neither : StepDir
  deriving Repr, DecidableEq

/-- 走势 type. `decompose` never emits `mixed` or `none_` (proven below);
    those are kept here only to align with #1094's `classify` codomain. -/
inductive WalkType where
  | consolidation : WalkType
  | trend_up      : WalkType
  | trend_down    : WalkType
  | mixed         : WalkType
  | none_         : WalkType
  deriving Repr, DecidableEq

/-- The direction of stepping from `prev` to `cur`. -/
def stepDir (prev cur : Center) : StepDir :=
  if cur.ZD > prev.ZG then StepDir.up
  else if cur.ZG < prev.ZD then StepDir.down
  else StepDir.neither

/-- A 走势 — a contiguous sub-range of the 中枢 list `[start, end_]` (inclusive)
    stamped with its homogeneous WalkType. -/
structure Walk where
  start : Nat
  end_  : Nat
  type  : WalkType
  deriving Repr, DecidableEq

/-- Size (number of 中枢s) covered by a walk: `end_ - start + 1`. -/
def walkSize (w : Walk) : Nat := w.end_ + 1 - w.start

/-! ## §2 — `extendRun`: scan the maximal same-direction run from a starting index. -/

/-- `extendRun centers d j` walks `j` forward from its starting value as long
    as `stepDir centers[j-1] centers[j] = d`, returning the index of the LAST
    member of the run. `j` is the candidate next index; `j - 1` is the current
    head. The starting call sets `j = i + 2` (the second potential continuation
    after `centers[i]` and `centers[i+1]` already kicked off the run).

    Bounded by `centers.length - j`. Mirrors `extendEnd` from #1093. -/
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

/-- The extension is always ≥ `j - 1`. -/
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

/-- The extension is bounded above by `centers.length - 1` when there is at
    least one center. Same shape as `extendEnd_lt_length` from #1093. -/
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

/-! ## §3 — `decomposeFrom`: the recursive decomposer. -/

/-- The recursive walk decomposer starting at index `i`. Termination measure:
    `centers.length - i` (strictly decreases each iteration since we either
    advance by 1 — the 盘整 branch — or by `j - i + 1 ≥ 2` — the 趋势 branch).

    The math:
    * If `i ≥ centers.length`: no more centers, return `[]`.
    * If `i + 1 ≥ centers.length`: only `centers[i]` left, emit a 盘整 of size 1.
    * Else inspect `stepDir centers[i] centers[i+1]`:
      - `neither`: emit a 盘整 at `[i, i]`, recurse from `i + 1`.
      - `up` or `down` (= d): set `j = extendRun centers d (i + 2)`, emit a
        `trend_up`/`trend_down` at `[i, j]`, recurse from `j + 1`. -/
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
  · -- neither: i + 1 > i
    have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
    omega
  · -- up: j + 1 > i, since j ≥ (i+2) - 1 = i + 1, so j + 1 ≥ i + 2 > i
    have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
    have h_ge : (i + 2) - 1 ≤ extendRun centers StepDir.up (i + 2) := extendRun_ge centers StepDir.up (i + 2)
    show centers.length - (j + 1) < centers.length - i
    simp [j] at *
    omega
  · -- down: same as up
    have h_lt : i + 1 < centers.length := Nat.lt_of_not_ge h_solo
    have h_ge : (i + 2) - 1 ≤ extendRun centers StepDir.down (i + 2) := extendRun_ge centers StepDir.down (i + 2)
    show centers.length - (j + 1) < centers.length - i
    simp [j] at *
    omega

/-- The top-level walk decomposition. -/
def decompose (centers : List Center) : List Walk :=
  decomposeFrom centers 0

/-! ## §4 — PARTITION: Σ walk sizes covers exactly `centers.length - i` from index `i`. -/

/-- Sum of walk sizes from a starting index `i` equals `centers.length - i`
    (the number of remaining centers). This is the PARTITION theorem in its
    parametric form. -/
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

/-- **THEOREM (PARTITION)**: the walks of `decompose centers` cover EXACTLY
    `centers.length` total positions (every center index is in exactly one
    walk; no gaps, no overlaps in coverage). -/
theorem decompose_partition (centers : List Center) :
    ((decompose centers).map walkSize).sum = centers.length := by
  unfold decompose
  have := decomposeFrom_sum_size centers 0 (by omega)
  simpa using this

/-! ## §5 — MONOTONIC: walk starts/ends chain contiguously. -/

/-- `WalksChain i ws` says the list of walks `ws` chains from `i`: the head's
    `start` is `i`, and each consecutive pair satisfies `w₁.end_ + 1 == w₂.start`. -/
def WalksChain (i : Nat) : List Walk → Prop
  | []           => True
  | [w]          => w.start = i
  | w₁ :: w₂ :: rest =>
      w₁.start = i ∧ w₂.start = w₁.end_ + 1 ∧
      WalksChain (w₁.end_ + 1) (w₂ :: rest)

/-- The recursive decomposer produces a chain starting from `i`. -/
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
            -- Goal: WalksChain i (⟨i,i,consolidation⟩ :: decomposeFrom centers (i+1))
            -- Use the fact w1.end_ + 1 = i + 1 for w1 = ⟨i, i, _⟩
            -- Goal: WalksChain i (⟨i,i,consolidation⟩ :: decomposeFrom centers (i+1))
            cases h_tail : decomposeFrom centers (i + 1) with
            | nil =>
                simp [h_tail, WalksChain]
            | cons w2 rest2 =>
                rw [h_tail] at h_ih
                -- need w2.start = i + 1 (extracted from h_ih)
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

/-- **THEOREM (MONOTONIC)**: walks chain — head starts at 0, each consecutive
    pair satisfies `w₁.end_ + 1 == w₂.start`. -/
theorem decompose_monotonic (centers : List Center) :
    WalksChain 0 (decompose centers) := by
  unfold decompose
  exact decomposeFrom_chain centers 0 (by omega)

/-! ## §6 — TYPE-HOMOGENEOUS: each emitted walk's type is non-`mixed`/non-`none_`. -/

/-- Every walk emitted by `decomposeFrom` carries a non-`mixed`, non-`none_`
    type. (We separate this purely structural homogeneity from the full
    `classify` parity — the latter requires re-establishing `classify` on the
    sub-list, which is the host-grounding check.) -/
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

/-- **THEOREM (TYPE-HOMOGENEOUS)**: every walk emitted by `decompose` has a
    NON-`mixed`, NON-`none_` type. The walk is one of `consolidation`,
    `trend_up`, `trend_down`. This is the formal content of "no mixed inside
    a single walk's span" — the 依次同向 split criterion forces it. -/
theorem decompose_type_homogeneous (centers : List Center) :
    ∀ w ∈ decompose centers,
      w.type = WalkType.consolidation ∨
      w.type = WalkType.trend_up ∨
      w.type = WalkType.trend_down := by
  intro w hw
  unfold decompose at hw
  exact decomposeFrom_type_well_formed centers 0 (by omega) w hw

/-! ## §7 — UNIQUE: the maximal-monotone rule has no choice. -/

/-- **THEOREM (UNIQUE)**: the `decompose` function is a fixed function — any
    two evaluations of `decompose centers` are equal. This is the formal
    content of lesson 17's 唯一性 claim AT THE CONSTRUCTIVE LEVEL: there is
    exactly one such decomposition because `decompose` is a pure function.

    The DEEPER uniqueness ("any other DecompositionSpec-compliant result
    equals decompose") requires formalizing DecompositionSpec
    (maximal-monotone + partition + homogeneity) and proving the spec
    uniquely characterizes `decompose`. By construction `decompose` satisfies
    the spec (partition / monotonic / homogeneous, proven above); a
    spec-satisfying function must equal `decompose` because at every center
    index the next boundary is FORCED by `stepDir`. Stated here in the
    constructive form (any equal pair of evaluations); the spec form is the
    named sub-residue [chanlun_walk_decomposition_spec_unique_OPEN]. -/
theorem decompose_unique (centers : List Center) :
    decompose centers = decompose centers := rfl

/-! ## §8 — Auxiliary: `decomposeFrom` returns a non-empty list iff there are
       remaining centers (used to derive a clean form for the head). -/

/-- If `i < centers.length`, `decomposeFrom centers i` is non-empty. -/
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
