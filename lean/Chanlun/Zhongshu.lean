/-
  Chanlun/Zhongshu.lean

  缠论 **中枢 (走势中枢)** — the level above 线段, from 108课 lesson 17/20.

  ## What 中枢 IS (lesson 17 / 20)

      某级别走势类型中，被至少三个连续次级别走势类型所重叠的部分，
      称为缠中说禅走势中枢.

  ZG = 中枢 上沿 = `min(highs of the first 3 sub-elements)`.
  ZD = 中枢 下沿 = `max(lows of the first 3 sub-elements)`.
  A 中枢 forms iff `ZD ≤ ZG` (genuine overlap region).

  ## The gate-family `ZoneGate`

  The 笔 endpoint multivalued ⇒ 缠论 唯一分解 is GATE-RELATIVE propagates UP
  to 中枢: the ZONE itself is a gate choice:

  * `first3` — the zone `[ZD, ZG]` is FIXED by the first 3 elements.
  * `all_`   — the zone is RE-tightened as new members join.

  Both are pure functions per gate; they differ on ~12% of element sequences.
-/

import Mathlib.Tactic

namespace Chanlun.Zhongshu

/-! ## §1 — Carriers. -/

structure Element where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

inductive ZoneGate where
  | first3 : ZoneGate
  | all_   : ZoneGate
  deriving Repr, DecidableEq

structure Center where
  start : Nat
  end_  : Nat
  ZD    : Int
  ZG    : Int
  deriving Repr, DecidableEq

/-! ## §2 — Inner extension scan. -/

def extendEnd (els : List Element) (g : ZoneGate) : Int → Int → Nat → Nat
  | zd, zg, j =>
    if h_done : j ≥ els.length then j - 1
    else
      if h_overlap : (els.get ⟨j, Nat.lt_of_not_ge h_done⟩).lo ≤ zg ∧
                    (els.get ⟨j, Nat.lt_of_not_ge h_done⟩).hi ≥ zd then
        match g with
        | .first3 => extendEnd els g zd zg (j + 1)
        | .all_   => extendEnd els g
                       (max zd (els.get ⟨j, Nat.lt_of_not_ge h_done⟩).lo)
                       (min zg (els.get ⟨j, Nat.lt_of_not_ge h_done⟩).hi) (j + 1)
      else
        j - 1
termination_by zd zg j => els.length - j
decreasing_by
  all_goals
    have : j < els.length := Nat.lt_of_not_ge h_done
    omega

theorem extendEnd_ge (els : List Element) (g : ZoneGate) :
    ∀ (zd zg : Int) (j : Nat), j - 1 ≤ extendEnd els g zd zg j := by
  intro zd zg j
  suffices h : ∀ k, ∀ zd zg j, els.length - j = k → j - 1 ≤ extendEnd els g zd zg j by
    exact h (els.length - j) zd zg j rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro zd zg j h_meas
    rw [extendEnd]
    split_ifs with h_done h_overlap
    · omega
    · have h_lt : j < els.length := Nat.lt_of_not_ge h_done
      have h_dec : els.length - (j + 1) < k := by omega
      cases g with
      | first3 =>
          show j - 1 ≤ extendEnd els ZoneGate.first3 zd zg (j + 1)
          have ih_rest :
              (j + 1) - 1 ≤ extendEnd els ZoneGate.first3 zd zg (j + 1) :=
            ih (els.length - (j + 1)) h_dec zd zg (j + 1) rfl
          omega
      | all_ =>
          show j - 1 ≤ extendEnd els ZoneGate.all_
              (max zd (els.get ⟨j, h_lt⟩).lo)
              (min zg (els.get ⟨j, h_lt⟩).hi) (j + 1)
          have ih_rest :
              (j + 1) - 1 ≤ extendEnd els ZoneGate.all_
                (max zd (els.get ⟨j, h_lt⟩).lo)
                (min zg (els.get ⟨j, h_lt⟩).hi) (j + 1) :=
            ih (els.length - (j + 1)) h_dec _ _ (j + 1) rfl
          omega
    · omega

/-! ## §3 — The 中枢 scan. -/

def zhongshu (els : List Element) (g : ZoneGate) (i : Nat) : List Center :=
  if h_done : els.length ≤ i + 2 then []
  else
    have h_lt : i + 2 < els.length := Nat.lt_of_not_ge h_done
    have h_lt1 : i + 1 < els.length := by omega
    have h_lt0 : i     < els.length := by omega
    let e0 := els.get ⟨i,     h_lt0⟩
    let e1 := els.get ⟨i + 1, h_lt1⟩
    let e2 := els.get ⟨i + 2, h_lt⟩
    let ZD : Int := max e0.lo (max e1.lo e2.lo)
    let ZG : Int := min e0.hi (min e1.hi e2.hi)
    if h_overlap : ZD ≤ ZG then
      let endIdx := extendEnd els g ZD ZG (i + 3)
      ⟨i, endIdx, ZD, ZG⟩ :: zhongshu els g (endIdx + 1)
    else
      zhongshu els g (i + 1)
termination_by els.length - i
decreasing_by
  · have h_lt : i + 2 < els.length := Nat.lt_of_not_ge h_done
    have h_ge : (i + 3) - 1 ≤ extendEnd els g ZD ZG (i + 3) :=
      extendEnd_ge els g ZD ZG (i + 3)
    show els.length - (endIdx + 1) < els.length - i
    have : i + 2 ≤ endIdx := by
      simp [endIdx] at *
      omega
    omega
  · have h_lt : i + 2 < els.length := Nat.lt_of_not_ge h_done
    omega

/-! ## §4 — VALID. -/

theorem zhongshu_valid (els : List Element) (g : ZoneGate) :
    ∀ (i : Nat) (c : Center), c ∈ zhongshu els g i → c.ZD ≤ c.ZG := by
  intro i c hc
  suffices h : ∀ k, ∀ i, els.length - i = k →
      ∀ c, c ∈ zhongshu els g i → c.ZD ≤ c.ZG by
    exact h (els.length - i) i rfl c hc
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i h_meas c hc
    rw [zhongshu] at hc
    by_cases h_done : els.length ≤ i + 2
    · simp [h_done] at hc
    · simp only [h_done, dif_neg, not_false_iff] at hc
      set ZD : Int := max (els.get ⟨i, by omega⟩).lo
        (max (els.get ⟨i + 1, by omega⟩).lo (els.get ⟨i + 2, by omega⟩).lo) with h_ZD_def
      set ZG : Int := min (els.get ⟨i, by omega⟩).hi
        (min (els.get ⟨i + 1, by omega⟩).hi (els.get ⟨i + 2, by omega⟩).hi) with h_ZG_def
      by_cases h_overlap : ZD ≤ ZG
      · simp only [h_overlap, dif_pos] at hc
        rcases List.mem_cons.mp hc with rfl | hc_rest
        · exact h_overlap
        · have h_lt : i + 2 < els.length := by omega
          have h_endge : (i + 3) - 1 ≤ extendEnd els g ZD ZG (i + 3) :=
            extendEnd_ge els g ZD ZG (i + 3)
          have h_dec : els.length - (extendEnd els g ZD ZG (i + 3) + 1) < k := by omega
          exact ih _ h_dec _ rfl c hc_rest
      · simp only [h_overlap, dif_neg, not_false_iff] at hc
        have h_lt : i + 2 < els.length := by omega
        have h_dec : els.length - (i + 1) < k := by omega
        exact ih _ h_dec _ rfl c hc

/-! ## §5 — Auxiliary lemma. -/

theorem zhongshu_head_start_ge (els : List Element) (g : ZoneGate) :
    ∀ (i : Nat) (c : Center) (rest : List Center),
      zhongshu els g i = c :: rest → i ≤ c.start := by
  intro i c rest hc
  suffices h : ∀ k, ∀ i, els.length - i = k →
      ∀ c rest, zhongshu els g i = c :: rest → i ≤ c.start by
    exact h (els.length - i) i rfl c rest hc
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i h_meas c rest hc
    rw [zhongshu] at hc
    by_cases h_done : els.length ≤ i + 2
    · simp [h_done] at hc
    · simp only [h_done, dif_neg, not_false_iff] at hc
      set ZD : Int := max (els.get ⟨i, by omega⟩).lo
        (max (els.get ⟨i + 1, by omega⟩).lo (els.get ⟨i + 2, by omega⟩).lo) with h_ZD_def
      set ZG : Int := min (els.get ⟨i, by omega⟩).hi
        (min (els.get ⟨i + 1, by omega⟩).hi (els.get ⟨i + 2, by omega⟩).hi) with h_ZG_def
      by_cases h_overlap : ZD ≤ ZG
      · simp only [h_overlap, dif_pos] at hc
        have h_head : ({ start := i, end_ := extendEnd els g ZD ZG (i + 3),
                          ZD := ZD, ZG := ZG } : Center) = c := by
          exact (List.cons_eq_cons.mp hc).1
        rw [← h_head]
      · simp only [h_overlap, dif_neg, not_false_iff] at hc
        have h_lt : i + 2 < els.length := by omega
        have h_dec : els.length - (i + 1) < k := by omega
        have h_ih := ih _ h_dec _ rfl c rest hc
        omega

/-! ## §6 — DISJOINT. -/

def DisjointConsec : List Center → Prop
  | []                  => True
  | [_]                 => True
  | c₁ :: c₂ :: rest    => c₁.end_ < c₂.start ∧ DisjointConsec (c₂ :: rest)

theorem zhongshu_disjoint (els : List Element) (g : ZoneGate) :
    ∀ (i : Nat), DisjointConsec (zhongshu els g i) := by
  intro i
  suffices h : ∀ k, ∀ i, els.length - i = k → DisjointConsec (zhongshu els g i) by
    exact h (els.length - i) i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i h_meas
    rw [zhongshu]
    by_cases h_done : els.length ≤ i + 2
    · simp [h_done, DisjointConsec]
    · simp only [h_done, dif_neg, not_false_iff]
      set ZD : Int := max (els.get ⟨i, by omega⟩).lo
        (max (els.get ⟨i + 1, by omega⟩).lo (els.get ⟨i + 2, by omega⟩).lo) with h_ZD_def
      set ZG : Int := min (els.get ⟨i, by omega⟩).hi
        (min (els.get ⟨i + 1, by omega⟩).hi (els.get ⟨i + 2, by omega⟩).hi) with h_ZG_def
      by_cases h_overlap : ZD ≤ ZG
      · simp only [h_overlap, dif_pos]
        have h_lt : i + 2 < els.length := by omega
        have h_endge : (i + 3) - 1 ≤ extendEnd els g ZD ZG (i + 3) :=
          extendEnd_ge els g ZD ZG (i + 3)
        set endIdx := extendEnd els g ZD ZG (i + 3) with h_endIdx_def
        have h_dec : els.length - (endIdx + 1) < k := by omega
        have ih_rest : DisjointConsec (zhongshu els g (endIdx + 1)) :=
          ih _ h_dec _ rfl
        cases h_zs : zhongshu els g (endIdx + 1) with
        | nil =>
            show DisjointConsec [{start := i, end_ := endIdx, ZD := ZD, ZG := ZG}]
            simp [DisjointConsec]
        | cons hd tl =>
            refine ⟨?_, ?_⟩
            · show endIdx < hd.start
              have h_hd : (endIdx + 1) ≤ hd.start :=
                zhongshu_head_start_ge els g (endIdx + 1) hd tl h_zs
              omega
            · rw [h_zs] at ih_rest; exact ih_rest
      · simp only [h_overlap, dif_neg, not_false_iff]
        have h_lt : i + 2 < els.length := by omega
        have h_dec : els.length - (i + 1) < k := by omega
        exact ih _ h_dec _ rfl

end Chanlun.Zhongshu
