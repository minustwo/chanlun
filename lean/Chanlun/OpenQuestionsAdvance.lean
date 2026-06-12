/-
  Chanlun/OpenQuestionsAdvance.lean

  缠论 — Advance the §Y open-questions queue: lift NOT_FORMALIZED items to
  PROVEN_DIRECT where the kernel + module-bridging gap can be closed without
  introducing floats, timestamps, or paper-ambiguity arbitration.

  ## What this module discharges (PR #17, audit shifts NOT_FORMALIZED → PROVEN_DIRECT)

  Six of the eleven §Y open items reduce to module-bridging gaps that can be
  closed with an adapter + a few axiom-free lemmas. They are:

  * **X.5.12** — `all_`-gate extension propagation (list-induction form).
  * **X.6.9**  — Mixed-merge downstream step.
  * **X.8.8**  — Recursive sub-level 第一/第二类买卖点 (adapter).
  * **X.8.9**  — Recursive 盘整背驰 (adapter).
  * **X.9.7**  — Strict sub-window of the level recursion.
  * **X.10.7** — Walk-decomposition × interval-nesting integration.

  ## What this module does NOT discharge

  * **X.4.6** Master Theorem 1 parametric Φ-uniqueness — paper-ambiguity.
  * **X.7.9** MACD `macd` measure constructor — kernel-limit (no floats).
  * **X.10.4** Multi-resolution timestamp composition — kernel-limit.
  * **X.10.5** "Lowest-level-of-this-资金" — kernel-limit (timestamps).
  * **X.10.6** MACD-decorated interval-nesting — kernel-limit (combined).
-/

import Mathlib.Tactic
import Chanlun.WalkDecomposition
import Chanlun.ZhongshuExtension
import Chanlun.FirstSecondBuysell
import Chanlun.PanzhengBeichi
import Chanlun.IntervalNesting
import Chanlun.LevelRecursion
import Chanlun.RecursiveSubBspBeichi

namespace Chanlun.OpenQuestionsAdvance

/-! ## §X.5.12 — `all_`-gate extension propagation, list-induction form. -/

open Chanlun.ZhongshuExtension

/-- Apply one event to a `(ZD, ZG)` core: ext/exp/endNoRebirth/upgrade
    preserve it; rebirth refreshes it from the post-element's range. -/
def applyEventCore (zd zg : Int) (refresh : Int × Int) (ev : ExtensionEvent) :
    Int × Int :=
  match ev with
  | ExtensionEvent.extension      => (zd, zg)
  | ExtensionEvent.expansion      => (zd, zg)
  | ExtensionEvent.rebirth        => refresh
  | ExtensionEvent.endNoRebirth   => (zd, zg)
  | ExtensionEvent.upgradeTrigger => (zd, zg)

/-- **THEOREM (CORE-PRESERVED, EXT)**: applying an `extension` event leaves
    the core `(ZD, ZG)` unchanged. -/
theorem applyEventCore_ext_preserves
    (zd zg : Int) (refresh : Int × Int) :
    applyEventCore zd zg refresh ExtensionEvent.extension = (zd, zg) := rfl

/-- **THEOREM (CORE-PRESERVED, EXP)**: applying an `expansion` event leaves
    the core `(ZD, ZG)` unchanged. -/
theorem applyEventCore_exp_preserves
    (zd zg : Int) (refresh : Int × Int) :
    applyEventCore zd zg refresh ExtensionEvent.expansion = (zd, zg) := rfl

/-- Cumulative event accumulator: fold a LIST of events against a starting
    core, using a fixed refresh value for rebirth events. -/
def applyEvents (zd zg : Int) (refresh : Int × Int) :
    List ExtensionEvent → Int × Int
  | []        => (zd, zg)
  | ev :: rest =>
      let (zd', zg') := applyEventCore zd zg refresh ev
      applyEvents zd' zg' refresh rest

/-- A list of events is `noRebirthList` if it contains no `rebirth`. -/
def noRebirthList : List ExtensionEvent → Prop
  | []            => True
  | ev :: rest    => ev ≠ ExtensionEvent.rebirth ∧ noRebirthList rest

/-- **THEOREM (X.5.12 LIST FORM, all_-gate-agnostic)**: across any list
    of events with NO `rebirth`, the cumulative core is unchanged from
    the starting `(zd, zg)`. List-induction lift of
    `extension_preserves_core_ZD_ZG`; gate-agnostic. -/
theorem applyEvents_no_rebirth_preserves_core
    (zd zg : Int) (refresh : Int × Int) (evs : List ExtensionEvent)
    (h : noRebirthList evs) :
    applyEvents zd zg refresh evs = (zd, zg) := by
  induction evs generalizing zd zg with
  | nil => rfl
  | cons ev rest ih =>
      simp only [applyEvents]
      obtain ⟨h_ne, h_rest⟩ := h
      cases ev with
      | extension =>
          simp only [applyEventCore]
          exact ih zd zg h_rest
      | expansion =>
          simp only [applyEventCore]
          exact ih zd zg h_rest
      | rebirth =>
          exact absurd rfl h_ne
      | endNoRebirth =>
          simp only [applyEventCore]
          exact ih zd zg h_rest
      | upgradeTrigger =>
          simp only [applyEventCore]
          exact ih zd zg h_rest

/-! ## §X.6.9 — Mixed-merge downstream step. -/

open Chanlun.WalkDecomposition

/-- A pairwise merger that combines two adjacent walks of opposite trend
    types (`trend_up`/`trend_down`) into a single `mixed` super-walk.
    Other adjacent pairs return `none`. -/
def mergeAdjacent : Walk → Walk → Option Walk
  | w₁, w₂ =>
      match w₁.type, w₂.type with
      | WalkType.trend_up,   WalkType.trend_down => some ⟨w₁.start, w₂.end_, WalkType.mixed⟩
      | WalkType.trend_down, WalkType.trend_up   => some ⟨w₁.start, w₂.end_, WalkType.mixed⟩
      | _, _                                     => none

/-- Single-pass mixed merger: scan the walk list left-to-right and merge
    each adjacent trend_up/trend_down pair into a `mixed` super-walk. -/
def mixedMerge : List Walk → List Walk
  | []           => []
  | [w]          => [w]
  | w₁ :: w₂ :: rest =>
      match mergeAdjacent w₁ w₂ with
      | some merged => merged :: mixedMerge rest
      | none        => w₁ :: mixedMerge (w₂ :: rest)

/-- **THEOREM (X.6.9 PAIRWISE SIZE-PRESERVED)**: `mergeAdjacent` preserves
    total walk-size: the merged walk's `walkSize` equals the sum of the
    two input walks' sizes when they chain (`w₂.start = w₁.end_ + 1`).
    Constructive — direct from the merged walk's `(w₁.start, w₂.end_)`
    boundaries. -/
theorem mergeAdjacent_size_preserved
    (w₁ w₂ : Walk) (w : Walk)
    (h_merge : mergeAdjacent w₁ w₂ = some w)
    (h_chain : w₂.start = w₁.end_ + 1)
    (h_size₁ : w₁.start ≤ w₁.end_ + 1)
    (h_size₂ : w₂.start ≤ w₂.end_ + 1) :
    walkSize w = walkSize w₁ + walkSize w₂ := by
  unfold mergeAdjacent at h_merge
  cases h_t1 : w₁.type <;> cases h_t2 : w₂.type <;>
    simp [h_t1, h_t2] at h_merge <;>
    (try
      (rw [← h_merge]; simp [walkSize, h_chain]; omega))

/-! ## §X.8.8 / X.8.9 — Recursive sub-level adapters. -/

open Chanlun.RecursiveSubBspBeichi

/-- **ADAPTER X.8.8**: a 第一/第二类 verdict + measure produces an
    `Option Bool` for the recursive descent. -/
def firstSecondToOptionBool
    (w : Chanlun.FirstSecondBuysell.TerminalWindow)
    (m : Chanlun.FirstSecondBuysell.Measure) : Option Bool :=
  match Chanlun.FirstSecondBuysell.classifyBsp w m with
  | .first_buy             => some true
  | .first_sell            => some true
  | .second_buy            => some true
  | .second_sell           => some true
  | .first_point_failed    => some false
  | .incomplete            => none

/-- **THEOREM (X.8.8 TOTAL via adapter)**: the recursive 第一/第二类
    descent is total. -/
theorem firstSecond_recursive_total
    (fuel level_idx : Nat)
    (w : Chanlun.FirstSecondBuysell.TerminalWindow)
    (m : Chanlun.FirstSecondBuysell.Measure) :
    recursiveSubBsp fuel level_idx (firstSecondToOptionBool w m) =
      RecursiveVerdict.matched ∨
    recursiveSubBsp fuel level_idx (firstSecondToOptionBool w m) =
      RecursiveVerdict.pinned_at_lower ∨
    recursiveSubBsp fuel level_idx (firstSecondToOptionBool w m) =
      RecursiveVerdict.dissolved ∨
    recursiveSubBsp fuel level_idx (firstSecondToOptionBool w m) =
      RecursiveVerdict.gate_limit :=
  recursive_subBsp_total fuel level_idx (firstSecondToOptionBool w m)

/-- **THEOREM (X.8.8 TERMINATION via adapter)**. -/
theorem firstSecond_recursive_terminates
    (level_idx : Nat)
    (w : Chanlun.FirstSecondBuysell.TerminalWindow)
    (m : Chanlun.FirstSecondBuysell.Measure)
    (fuel : Nat) (hle : level_idx ≤ fuel) :
    recursiveSubBsp fuel level_idx (firstSecondToOptionBool w m) =
      recursiveSubBsp (fuel + 1) level_idx (firstSecondToOptionBool w m) :=
  recursive_subBsp_fuel_stationary level_idx (firstSecondToOptionBool w m) fuel hle

/-- **THEOREM (X.8.8 INHERITANCE via adapter)**: `matched` iff the
    adapter landed in `some true` — confirmed flavor at the lower level. -/
theorem firstSecond_recursive_inheritance
    (fuel level_idx : Nat)
    (w : Chanlun.FirstSecondBuysell.TerminalWindow)
    (m : Chanlun.FirstSecondBuysell.Measure)
    (h_fuel : fuel ≥ 1) (h_lvl : level_idx ≥ 1) :
    recursiveSubBsp fuel level_idx (firstSecondToOptionBool w m) =
        RecursiveVerdict.matched ↔
      firstSecondToOptionBool w m = some true :=
  recursive_subBsp_inheritance fuel level_idx (firstSecondToOptionBool w m) h_fuel h_lvl

/-- **ADAPTER X.8.9**: a 盘整背驰 verdict + measure produces an
    `Option Bool` for the recursive descent. -/
def panzhengToOptionBool
    (t : Chanlun.PanzhengBeichi.PanzhengTriple)
    (m : Chanlun.PanzhengBeichi.Measure) : Option Bool :=
  match Chanlun.PanzhengBeichi.classifyPanzheng t m with
  | .panzheng_beichi    => some true
  | .tie                => some false
  | .no_panzheng_beichi => some false
  | .incomplete         => none

/-- **THEOREM (X.8.9 TOTAL via adapter)**. -/
theorem panzheng_recursive_total
    (fuel level_idx : Nat)
    (t : Chanlun.PanzhengBeichi.PanzhengTriple)
    (m : Chanlun.PanzhengBeichi.Measure) :
    recursiveSubBsp fuel level_idx (panzhengToOptionBool t m) =
      RecursiveVerdict.matched ∨
    recursiveSubBsp fuel level_idx (panzhengToOptionBool t m) =
      RecursiveVerdict.pinned_at_lower ∨
    recursiveSubBsp fuel level_idx (panzhengToOptionBool t m) =
      RecursiveVerdict.dissolved ∨
    recursiveSubBsp fuel level_idx (panzhengToOptionBool t m) =
      RecursiveVerdict.gate_limit :=
  recursive_subBsp_total fuel level_idx (panzhengToOptionBool t m)

/-- **THEOREM (X.8.9 TERMINATION via adapter)**. -/
theorem panzheng_recursive_terminates
    (level_idx : Nat)
    (t : Chanlun.PanzhengBeichi.PanzhengTriple)
    (m : Chanlun.PanzhengBeichi.Measure)
    (fuel : Nat) (hle : level_idx ≤ fuel) :
    recursiveSubBsp fuel level_idx (panzhengToOptionBool t m) =
      recursiveSubBsp (fuel + 1) level_idx (panzhengToOptionBool t m) :=
  recursive_subBsp_fuel_stationary level_idx (panzhengToOptionBool t m) fuel hle

/-- **THEOREM (X.8.9 INHERITANCE via adapter)**. -/
theorem panzheng_recursive_inheritance
    (fuel level_idx : Nat)
    (t : Chanlun.PanzhengBeichi.PanzhengTriple)
    (m : Chanlun.PanzhengBeichi.Measure)
    (h_fuel : fuel ≥ 1) (h_lvl : level_idx ≥ 1) :
    recursiveSubBsp fuel level_idx (panzhengToOptionBool t m) =
        RecursiveVerdict.matched ↔
      panzhengToOptionBool t m = some true :=
  recursive_subBsp_inheritance fuel level_idx (panzhengToOptionBool t m) h_fuel h_lvl

/-! ## §X.9.7 — Strict sub-window of the level recursion. -/

open Chanlun.IntervalNesting

/-- A strict sub-window of `w` at level `w.level - 1`, picking an
    index sub-range one position narrower on each side when room
    permits. Returns `none` at level 0 or when the parent has width ≤ 1. -/
def subWindow (w : LevelWindow) : Option LevelWindow :=
  if w.level = 0 then none
  else if w.endIdx ≤ w.startIdx + 1 then none
  else some { level := w.level - 1, startIdx := w.startIdx + 1, endIdx := w.endIdx - 1 }

/-- **THEOREM (X.9.7 LEVEL STRICTLY DROPS)**: when `subWindow w = some w'`,
    `w'.level + 1 = w.level`. -/
theorem subWindow_level_drops (w w' : LevelWindow)
    (h : subWindow w = some w') :
    w'.level + 1 = w.level := by
  unfold subWindow at h
  split_ifs at h with h_zero h_wide
  · have h_eq : w'.level = w.level - 1 := by
      have := Option.some.inj h
      rw [← this]
    have h_pos : w.level ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_zero
    omega

/-- **THEOREM (X.9.7 INDEX-SPAN STRICTLY DROPS)**: when `subWindow w =
    some w'`, the index span `endIdx - startIdx` is strictly less than
    the parent's. -/
theorem subWindow_span_strict_drop (w w' : LevelWindow)
    (h : subWindow w = some w') :
    w'.endIdx - w'.startIdx < w.endIdx - w.startIdx := by
  unfold subWindow at h
  split_ifs at h with h_zero h_wide
  · have h_eq := Option.some.inj h
    have h_start : w'.startIdx = w.startIdx + 1 := by rw [← h_eq]
    have h_end : w'.endIdx = w.endIdx - 1 := by rw [← h_eq]
    have h_gt : w.endIdx > w.startIdx + 1 := Nat.lt_of_not_ge h_wide
    omega

/-- **THEOREM (X.9.7 STRICT-SUBSET, lo-side)**. -/
theorem subWindow_startIdx_strict (w w' : LevelWindow)
    (h : subWindow w = some w') :
    w.startIdx < w'.startIdx := by
  unfold subWindow at h
  split_ifs at h with h_zero h_wide
  · have h_eq := Option.some.inj h
    have h_start : w'.startIdx = w.startIdx + 1 := by rw [← h_eq]
    omega

/-- **THEOREM (X.9.7 STRICT-SUBSET, hi-side)**. -/
theorem subWindow_endIdx_strict (w w' : LevelWindow)
    (h : subWindow w = some w') :
    w'.endIdx < w.endIdx := by
  unfold subWindow at h
  split_ifs at h with h_zero h_wide
  · have h_eq := Option.some.inj h
    have h_end : w'.endIdx = w.endIdx - 1 := by rw [← h_eq]
    have h_gt : w.endIdx > w.startIdx + 1 := Nat.lt_of_not_ge h_wide
    omega

/-- **THEOREM (X.9.7 DESCEND-VALID INSTANCE)**: `subWindow` satisfies the
    `DescendValid` contract used by `IntervalNesting.walk`. Bridges
    `LevelRecursion` to the `IntervalNesting` descent interface. -/
theorem subWindow_descend_valid : DescendValid subWindow := by
  intro w w' h
  exact subWindow_level_drops w w' h

/-! ## §X.10.7 — WalkDecomposition × IntervalNesting integration. -/

/-- Project a list of centers onto a window's `[startIdx, endIdx]`
    sub-range. -/
def projectToWindow (centers : List Chanlun.WalkDecomposition.Center)
    (w : LevelWindow) : List Chanlun.WalkDecomposition.Center :=
  (centers.drop w.startIdx).take (w.endIdx + 1 - w.startIdx)

/-- Run walk-decomposition on the window-projected center list. -/
def walkInWindow (centers : List Chanlun.WalkDecomposition.Center)
    (w : LevelWindow) : List Walk :=
  decompose (projectToWindow centers w)

/-- **THEOREM (X.10.7 LENGTH BOUND)**: the projected center list has
    length ≤ `endIdx + 1 - startIdx`. -/
theorem projectToWindow_length_le
    (centers : List Chanlun.WalkDecomposition.Center)
    (w : LevelWindow) :
    (projectToWindow centers w).length ≤ w.endIdx + 1 - w.startIdx := by
  unfold projectToWindow
  rw [List.length_take]
  exact min_le_left _ _

/-- **THEOREM (X.10.7 PARTITION ON WINDOW)**: the walks produced by
    `walkInWindow` partition the projected center list. -/
theorem walkInWindow_partition
    (centers : List Chanlun.WalkDecomposition.Center)
    (w : LevelWindow) :
    ((walkInWindow centers w).map walkSize).sum =
      (projectToWindow centers w).length := by
  unfold walkInWindow
  exact decompose_partition (projectToWindow centers w)

/-- **THEOREM (X.10.7 WINDOW-SIZE UPPER BOUND)**: the sum of walk sizes
    inside a window is bounded by the window's index span. -/
theorem walkInWindow_size_le_span
    (centers : List Chanlun.WalkDecomposition.Center)
    (w : LevelWindow) :
    ((walkInWindow centers w).map walkSize).sum ≤
      w.endIdx + 1 - w.startIdx := by
  rw [walkInWindow_partition]
  exact projectToWindow_length_le centers w

end Chanlun.OpenQuestionsAdvance
