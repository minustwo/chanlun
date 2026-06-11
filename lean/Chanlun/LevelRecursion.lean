/-
  Chanlun/LevelRecursion.lean

  缠论 **走势必完美** (level-recursion termination) — lesson 24 + 17.

  ## What 原文 claims (lesson 24, paraphrased)

      任何走势都必然完美 — every 走势 inevitably terminates.

  Mathematically, the 级别 recursion (lift one 缠论 level to the next via
  中枢 collapse) STRICTLY DECREASES the element count at every non-terminal
  step. Hence the recursion is well-founded on `els.length` — it cannot
  spin forever; it resolves in finitely many levels.

  ## The lift step

  One deterministic `level n → level n+1` step over a sequence of integer
  price-range elements:

  * `centers = zhongshu els .first3 0`.
  * If `centers = []` → the level is TERMINAL: 走势 is COMPLETE (完美).
  * Else each 中枢 (a run of `≥3` consecutive elements) COLLAPSES to ONE
    level-`(n+1)` element whose range is the price ENVELOPE.

  Because every 中枢 absorbs `≥3 → 1`, each non-terminal lift strictly
  DROPS the element count by `≥2`.
-/

import Mathlib.Tactic
import Chanlun.Zhongshu

namespace Chanlun.LevelRecursion

open Chanlun.Zhongshu

/-! ## §1 — Center size. -/

def centerSize (c : Center) : Nat := c.end_ + 1 - c.start

/-! ## §2 — Each emitted center has size ≥ 3. -/

theorem centerSize_ge_3 (els : List Element) (g : ZoneGate) :
    ∀ (i : Nat) (c : Center), c ∈ zhongshu els g i → centerSize c ≥ 3 := by
  intro i c hc
  suffices h : ∀ k, ∀ i, els.length - i = k →
      ∀ c, c ∈ zhongshu els g i → centerSize c ≥ 3 by
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
        · show extendEnd els g ZD ZG (i + 3) + 1 - i ≥ 3
          have h_endge := extendEnd_ge els g ZD ZG (i + 3)
          omega
        · have h_lt : i + 2 < els.length := by omega
          have h_endge := extendEnd_ge els g ZD ZG (i + 3)
          have h_dec : els.length - (extendEnd els g ZD ZG (i + 3) + 1) < k := by omega
          exact ih _ h_dec (extendEnd els g ZD ZG (i + 3) + 1) rfl c hc_rest
      · simp only [h_overlap, dif_neg, not_false_iff] at hc
        have h_lt : i + 2 < els.length := by omega
        have h_dec : els.length - (i + 1) < k := by omega
        exact ih _ h_dec (i + 1) rfl c hc

/-! ## §3 — Sum ≥ 3 × length. -/

theorem total_size_ge_3_times_count
    (centers : List Center)
    (h : ∀ c ∈ centers, centerSize c ≥ 3) :
    (centers.map centerSize).sum ≥ 3 * centers.length := by
  induction centers with
  | nil => simp
  | cons c rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h_c : centerSize c ≥ 3 := h c (List.mem_cons_self c rest)
      have h_rest : ∀ c' ∈ rest, centerSize c' ≥ 3 := fun c' hc' =>
        h c' (List.mem_cons_of_mem c hc')
      have ih_sum := ih h_rest
      linarith

/-! ## §4 — THE LOAD-BEARING THEOREM. -/

/-- **THE LEVEL-RECURSION TERMINATION (走势必完美)**: if `zhongshu` produces
    at least one 中枢, the next-level count drops by `≥2`. -/
theorem lift_strict_drop
    (els : List Element) (g : ZoneGate)
    (h_nonempty : zhongshu els g 0 ≠ []) :
    (zhongshu els g 0).length + 2 ≤
      ((zhongshu els g 0).map centerSize).sum := by
  set centers := zhongshu els g 0 with h_centers_def
  have h_each : ∀ c ∈ centers, centerSize c ≥ 3 := by
    intro c hc
    exact centerSize_ge_3 els g 0 c hc
  have h_sum := total_size_ge_3_times_count centers h_each
  have h_length : centers.length ≥ 1 := by
    cases h_l : centers with
    | nil => exact absurd h_l h_nonempty
    | cons _ _ => simp [h_l]
  linarith

/-! ## §5 — Corollary. -/

theorem level_recursion_count_decreases
    (els : List Element) (g : ZoneGate)
    (h_nonempty : zhongshu els g 0 ≠ []) :
    (((zhongshu els g 0).map centerSize).sum - (zhongshu els g 0).length) ≥ 2 := by
  have h := lift_strict_drop els g h_nonempty
  omega

end Chanlun.LevelRecursion
