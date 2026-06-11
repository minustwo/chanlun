/-
  Chanlun/TrendType.lean

  缠论 **走势类型** (盘整 / 趋势) — 108课 lesson 17.

  ## What the 原文 claims (lesson 17, verbatim)

      任何级别的所有走势，都能分解成趋势与盘整两类.
      某完成的走势类型只包含一个缠中说禅走势中枢，就称为…盘整.
      至少包含两个以上依次同向的缠中说禅走势中枢，就称为…趋势.

  Reading the 原文 mathematically:

  * **盘整 (consolidation)** = exactly one 中枢.
  * **趋势 (trend)** = ≥2 中枢s, ALL stepping in the same direction.
    * `上涨趋势`: every next 中枢 entirely above the previous (ZD_next > ZG_prev).
    * `下跌趋势`: every next 中枢 entirely below (ZG_next < ZD_prev).
  * **mixed** = ≥2 中枢s NOT 依次同向 — the never-silent residue.
-/

import Mathlib.Tactic

namespace Chanlun.TrendType

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

/-! ## §2 — Step direction and predicates. -/

def stepDir (prev cur : Center) : StepDir :=
  if cur.ZD > prev.ZG then StepDir.up
  else if cur.ZG < prev.ZD then StepDir.down
  else StepDir.neither

def allStepsAreUp : List Center → Prop
  | []           => True
  | [_]          => True
  | c₁ :: c₂ :: rest => stepDir c₁ c₂ = StepDir.up ∧ allStepsAreUp (c₂ :: rest)

def allStepsAreDown : List Center → Prop
  | []           => True
  | [_]          => True
  | c₁ :: c₂ :: rest => stepDir c₁ c₂ = StepDir.down ∧ allStepsAreDown (c₂ :: rest)

def allUp : List Center → Bool
  | []               => true
  | [_]              => true
  | c₁ :: c₂ :: rest =>
      decide (stepDir c₁ c₂ = StepDir.up) && allUp (c₂ :: rest)

def allDown : List Center → Bool
  | []               => true
  | [_]              => true
  | c₁ :: c₂ :: rest =>
      decide (stepDir c₁ c₂ = StepDir.down) && allDown (c₂ :: rest)

/-! ## §3 — The classifier. -/

def classify : List Center → WalkType
  | []           => WalkType.none_
  | [_]          => WalkType.consolidation
  | c₁ :: c₂ :: rest =>
      if allUp (c₁ :: c₂ :: rest) then WalkType.trend_up
      else if allDown (c₁ :: c₂ :: rest) then WalkType.trend_down
      else WalkType.mixed

/-! ## §4 — Totality. -/

theorem classify_total (cs : List Center) :
    classify cs = WalkType.none_ ∨
    classify cs = WalkType.consolidation ∨
    classify cs = WalkType.trend_up ∨
    classify cs = WalkType.trend_down ∨
    classify cs = WalkType.mixed := by
  match cs with
  | []               =>
      left; rfl
  | [_]              =>
      right; left; rfl
  | c₁ :: c₂ :: rest =>
      simp only [classify]
      by_cases h_up : allUp (c₁ :: c₂ :: rest) = true
      · simp [h_up]
      · by_cases h_down : allDown (c₁ :: c₂ :: rest) = true
        · simp [h_up, h_down]
        · simp [h_up, h_down]

/-! ## §5 — The substantive theorem: 趋势 is monotone. -/

theorem allUp_iff_allStepsAreUp (cs : List Center) :
    allUp cs = true ↔ allStepsAreUp cs := by
  induction cs with
  | nil =>
      simp [allUp, allStepsAreUp]
  | cons c rest ih =>
      cases rest with
      | nil =>
          simp [allUp, allStepsAreUp]
      | cons c₂ rest' =>
          simp only [allUp, allStepsAreUp]
          constructor
          · intro h
            rw [Bool.and_eq_true] at h
            obtain ⟨h_head, h_tail⟩ := h
            refine ⟨decide_eq_true_iff.mp h_head, ?_⟩
            exact (ih).mp h_tail
          · intro ⟨h_head, h_tail⟩
            rw [Bool.and_eq_true]
            refine ⟨decide_eq_true_iff.mpr h_head, ?_⟩
            exact (ih).mpr h_tail

theorem allDown_iff_allStepsAreDown (cs : List Center) :
    allDown cs = true ↔ allStepsAreDown cs := by
  induction cs with
  | nil =>
      simp [allDown, allStepsAreDown]
  | cons c rest ih =>
      cases rest with
      | nil =>
          simp [allDown, allStepsAreDown]
      | cons c₂ rest' =>
          simp only [allDown, allStepsAreDown]
          constructor
          · intro h
            rw [Bool.and_eq_true] at h
            obtain ⟨h_head, h_tail⟩ := h
            refine ⟨decide_eq_true_iff.mp h_head, ?_⟩
            exact (ih).mp h_tail
          · intro ⟨h_head, h_tail⟩
            rw [Bool.and_eq_true]
            refine ⟨decide_eq_true_iff.mpr h_head, ?_⟩
            exact (ih).mpr h_tail

theorem classify_trend_monotone_up (cs : List Center) :
    classify cs = WalkType.trend_up → allStepsAreUp cs := by
  intro h
  match cs with
  | []               =>
      simp [classify] at h
  | [_]              =>
      simp [classify] at h
  | c₁ :: c₂ :: rest =>
      simp only [classify] at h
      by_cases h_up : allUp (c₁ :: c₂ :: rest) = true
      · exact (allUp_iff_allStepsAreUp _).mp h_up
      · simp [h_up] at h
        by_cases h_down : allDown (c₁ :: c₂ :: rest) = true
        · simp [h_down] at h
        · simp [h_down] at h

theorem classify_trend_monotone_down (cs : List Center) :
    classify cs = WalkType.trend_down → allStepsAreDown cs := by
  intro h
  match cs with
  | []               =>
      simp [classify] at h
  | [_]              =>
      simp [classify] at h
  | c₁ :: c₂ :: rest =>
      simp only [classify] at h
      by_cases h_up : allUp (c₁ :: c₂ :: rest) = true
      · simp [h_up] at h
      · simp [h_up] at h
        by_cases h_down : allDown (c₁ :: c₂ :: rest) = true
        · exact (allDown_iff_allStepsAreDown _).mp h_down
        · simp [h_down] at h

theorem classify_trend_monotone (cs : List Center) :
    (classify cs = WalkType.trend_up → allStepsAreUp cs) ∧
    (classify cs = WalkType.trend_down → allStepsAreDown cs) :=
  ⟨classify_trend_monotone_up cs, classify_trend_monotone_down cs⟩

end Chanlun.TrendType
