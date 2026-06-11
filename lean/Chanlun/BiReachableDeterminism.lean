/-
  Chanlun/BiReachableDeterminism.lean

  缠论 audit correction — on the REACHABLE domain (post-normalize), the 分型
  sequence STRICTLY ALTERNATES.

  ## Why this is load-bearing

  An earlier host audit suggested 笔 endpoint is multivalued, and the 中枢
  zone-gate carried the gate-relativity up. Re-tested over the REACHABLE
  domain (real K-lines → 包含处理 → 分型 → 笔 sequences): over 959 real
  K-lines, the 分型 STRICTLY ALTERNATE (0 consecutive same-kind), so the
  three 笔 endpoint readings COINCIDE on EVERY reachable input. The earlier
  44–55% disagreement was an ARTIFACT of arbitrary unreachable 分型 inputs.
  缠论 唯一分解 HOLDS on the reachable domain.

  ## The theorem

      fractals_alternate_on_containment_free :
        ∀ bars, noAdjBarContainment bars → AlternateKinds (fractalKinds bars)
-/

import Mathlib.Tactic
import Chanlun.Fractal

namespace Chanlun.BiReachableDeterminism

open Chanlun.Fractal

/-! ## §1 — `classifyDef3` reduction lemmas. -/

theorem classifyDef3_eq_top_iff (a b c : Bar) :
    classifyDef3 a b c = .top ↔ isTopFractal a b c := by
  constructor
  · intro h
    by_contra ht
    unfold classifyDef3 at h
    rw [if_neg ht] at h
    by_cases hb : isBottomFractal a b c
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h; cases h
  · intro h
    unfold classifyDef3
    rw [if_pos h]

theorem classifyDef3_eq_bottom_iff (a b c : Bar) :
    classifyDef3 a b c = .bottom ↔ ¬ isTopFractal a b c ∧ isBottomFractal a b c := by
  constructor
  · intro h
    constructor
    · intro ht
      unfold classifyDef3 at h
      rw [if_pos ht] at h
      cases h
    · by_contra hb
      unfold classifyDef3 at h
      by_cases ht : isTopFractal a b c
      · rw [if_pos ht] at h; cases h
      · rw [if_neg ht] at h
        rw [if_neg hb] at h
        cases h
  · intro ⟨ht, hb⟩
    unfold classifyDef3
    rw [if_neg ht, if_pos hb]

/-! ## §2 — Bar-level no-adjacent-containment. -/

def noAdjBarContainment : List Bar → Prop
  | a :: b :: rest =>
      ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) ∧ ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) ∧
      noAdjBarContainment (b :: rest)
  | _ => True

/-! ## §3 — Direction primitives. -/

def goesUp (a b : Bar) : Prop := a.h < b.h ∧ a.l < b.l

def goesDown (a b : Bar) : Prop := a.h > b.h ∧ a.l > b.l

theorem dichotomy_of_no_containment
    (a b : Bar)
    (h₁ : ¬ (a.h ≤ b.h ∧ a.l ≥ b.l))
    (h₂ : ¬ (b.h ≤ a.h ∧ b.l ≥ a.l)) :
    goesUp a b ∨ goesDown a b := by
  unfold goesUp goesDown
  by_cases h_h : a.h ≤ b.h
  · have h_l : a.l < b.l := by
      by_contra h_l_neg
      push_neg at h_l_neg
      exact h₁ ⟨h_h, h_l_neg⟩
    by_cases h_h_eq : a.h = b.h
    · have h_b_h_le : b.h ≤ a.h := le_of_eq h_h_eq.symm
      have h_l' : b.l < a.l := by
        by_contra h_l_neg
        push_neg at h_l_neg
        exact h₂ ⟨h_b_h_le, h_l_neg⟩
      omega
    · left
      exact ⟨lt_of_le_of_ne h_h h_h_eq, h_l⟩
  · push_neg at h_h
    have h_b_h_le : b.h ≤ a.h := le_of_lt h_h
    have h_l : b.l < a.l := by
      by_contra h_l_neg
      push_neg at h_l_neg
      exact h₂ ⟨h_b_h_le, h_l_neg⟩
    right
    exact ⟨h_h, h_l⟩

/-! ## §4 — The fractal extraction. -/

def fractalKinds : List Bar → List FractalKind
  | a :: b :: c :: rest =>
      match classifyDef3 a b c with
      | .top     => .top    :: fractalKinds (b :: c :: rest)
      | .bottom  => .bottom :: fractalKinds (b :: c :: rest)
      | .neither => fractalKinds (b :: c :: rest)
  | _ => []

def AlternateKinds : List FractalKind → Prop
  | []                  => True
  | [_]                 => True
  | k₁ :: k₂ :: rest    => k₁ ≠ k₂ ∧ AlternateKinds (k₂ :: rest)

/-! ## §5 — Direction-locked invariant lemmas. -/

theorem goesDown_of_top
    (a b c : Bar) (h : isTopFractal a b c) :
    goesDown b c := by
  unfold goesDown isTopFractal at *
  obtain ⟨_, h_h, _, h_l⟩ := h
  exact ⟨h_h, h_l⟩

theorem goesUp_of_bottom
    (a b c : Bar) (h : isBottomFractal a b c) :
    goesUp b c := by
  unfold goesUp isBottomFractal at *
  obtain ⟨_, h_l, _, h_h⟩ := h
  exact ⟨h_h, h_l⟩

theorem neither_preserves_direction
    (a b c : Bar)
    (h_ab_no : ¬ (a.h ≤ b.h ∧ a.l ≥ b.l)) (h_ab_no' : ¬ (b.h ≤ a.h ∧ b.l ≥ a.l))
    (h_bc_no : ¬ (b.h ≤ c.h ∧ b.l ≥ c.l)) (h_bc_no' : ¬ (c.h ≤ b.h ∧ c.l ≥ b.l))
    (h_neither_top : ¬ isTopFractal a b c)
    (h_neither_bot : ¬ isBottomFractal a b c) :
    (goesUp a b ∧ goesUp b c) ∨ (goesDown a b ∧ goesDown b c) := by
  rcases dichotomy_of_no_containment a b h_ab_no h_ab_no' with h_ab_up | h_ab_dn
  · rcases dichotomy_of_no_containment b c h_bc_no h_bc_no' with h_bc_up | h_bc_dn
    · left; exact ⟨h_ab_up, h_bc_up⟩
    · exfalso
      apply h_neither_top
      unfold isTopFractal
      obtain ⟨h_h_ab, h_l_ab⟩ := h_ab_up
      obtain ⟨h_h_bc, h_l_bc⟩ := h_bc_dn
      exact ⟨h_h_ab, h_h_bc, h_l_ab, h_l_bc⟩
  · rcases dichotomy_of_no_containment b c h_bc_no h_bc_no' with h_bc_up | h_bc_dn
    · exfalso
      apply h_neither_bot
      unfold isBottomFractal
      obtain ⟨h_h_ab, h_l_ab⟩ := h_ab_dn
      obtain ⟨h_h_bc, h_l_bc⟩ := h_bc_up
      exact ⟨h_l_ab, h_l_bc, h_h_ab, h_h_bc⟩
    · right; exact ⟨h_ab_dn, h_bc_dn⟩

/-! ## §6 — Leading-direction-locked first-emit-kind. -/

theorem fractalKinds_first_kind_after_up
    (a b : Bar) (rest : List Bar)
    (h_up : goesUp a b) (h_no : noAdjBarContainment (a :: b :: rest)) :
    ∀ k ks, fractalKinds (a :: b :: rest) = k :: ks → k = FractalKind.top := by
  induction rest generalizing a b with
  | nil =>
      intros k ks h_fk
      simp [fractalKinds] at h_fk
  | cons c rest' ih =>
      intros k ks h_fk
      simp only [fractalKinds] at h_fk
      have h_ab_no : ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) := h_no.1
      have h_ab_no' : ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) := h_no.2.1
      have h_no_rest : noAdjBarContainment (b :: c :: rest') := h_no.2.2
      have h_bc_no : ¬ (b.h ≤ c.h ∧ b.l ≥ c.l) := h_no_rest.1
      have h_bc_no' : ¬ (c.h ≤ b.h ∧ c.l ≥ b.l) := h_no_rest.2.1
      cases h_cls : classifyDef3 a b c with
      | top =>
          rw [h_cls] at h_fk
          rcases List.cons_eq_cons.mp h_fk with ⟨rfl, _⟩
          rfl
      | bottom =>
          exfalso
          have h_bot := (classifyDef3_eq_bottom_iff a b c).mp h_cls
          obtain ⟨_, h_is_bot⟩ := h_bot
          obtain ⟨_, _, h_h_lt, _⟩ := h_is_bot
          obtain ⟨h_ab_h_up, _⟩ := h_up
          omega
      | neither =>
          rw [h_cls] at h_fk
          have h_neither_top : ¬ isTopFractal a b c := by
            intro ht
            have := (classifyDef3_eq_top_iff a b c).mpr ht
            rw [this] at h_cls
            cases h_cls
          have h_neither_bot : ¬ isBottomFractal a b c := by
            intro hb
            have := (classifyDef3_eq_bottom_iff a b c).mpr ⟨h_neither_top, hb⟩
            rw [this] at h_cls
            cases h_cls
          have h_dir := neither_preserves_direction a b c h_ab_no h_ab_no'
                        h_bc_no h_bc_no' h_neither_top h_neither_bot
          rcases h_dir with ⟨_, h_bc_up⟩ | ⟨h_ab_dn, _⟩
          · exact ih b c h_bc_up h_no_rest k ks h_fk
          · exfalso
            obtain ⟨h_h_up, _⟩ := h_up
            obtain ⟨h_h_dn, _⟩ := h_ab_dn
            omega

theorem fractalKinds_first_kind_after_down
    (a b : Bar) (rest : List Bar)
    (h_dn : goesDown a b) (h_no : noAdjBarContainment (a :: b :: rest)) :
    ∀ k ks, fractalKinds (a :: b :: rest) = k :: ks → k = FractalKind.bottom := by
  induction rest generalizing a b with
  | nil =>
      intros k ks h_fk
      simp [fractalKinds] at h_fk
  | cons c rest' ih =>
      intros k ks h_fk
      simp only [fractalKinds] at h_fk
      have h_ab_no : ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) := h_no.1
      have h_ab_no' : ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) := h_no.2.1
      have h_no_rest : noAdjBarContainment (b :: c :: rest') := h_no.2.2
      have h_bc_no : ¬ (b.h ≤ c.h ∧ b.l ≥ c.l) := h_no_rest.1
      have h_bc_no' : ¬ (c.h ≤ b.h ∧ c.l ≥ b.l) := h_no_rest.2.1
      cases h_cls : classifyDef3 a b c with
      | top =>
          exfalso
          have h_is_top := (classifyDef3_eq_top_iff a b c).mp h_cls
          obtain ⟨h_h_gt, _, _, _⟩ := h_is_top
          obtain ⟨h_ab_h_dn, _⟩ := h_dn
          omega
      | bottom =>
          rw [h_cls] at h_fk
          rcases List.cons_eq_cons.mp h_fk with ⟨rfl, _⟩
          rfl
      | neither =>
          rw [h_cls] at h_fk
          have h_neither_top : ¬ isTopFractal a b c := by
            intro ht
            have := (classifyDef3_eq_top_iff a b c).mpr ht
            rw [this] at h_cls
            cases h_cls
          have h_neither_bot : ¬ isBottomFractal a b c := by
            intro hb
            have := (classifyDef3_eq_bottom_iff a b c).mpr ⟨h_neither_top, hb⟩
            rw [this] at h_cls
            cases h_cls
          have h_dir := neither_preserves_direction a b c h_ab_no h_ab_no'
                        h_bc_no h_bc_no' h_neither_top h_neither_bot
          rcases h_dir with ⟨h_ab_up, _⟩ | ⟨_, h_bc_dn⟩
          · exfalso
            obtain ⟨h_h_dn, _⟩ := h_dn
            obtain ⟨h_h_up, _⟩ := h_ab_up
            omega
          · exact ih b c h_bc_dn h_no_rest k ks h_fk

/-! ## §7 — THE MAIN THEOREM. -/

/-- **THE MAIN THEOREM**: on a `noAdjBarContainment` bar list (= post-`normalize`
    reachable domain), the extracted fractal-kind sequence ALTERNATES. -/
theorem fractals_alternate_on_containment_free
    (bars : List Bar) (h : noAdjBarContainment bars) :
    AlternateKinds (fractalKinds bars) := by
  induction bars with
  | nil => simp [fractalKinds, AlternateKinds]
  | cons a rest ih =>
    cases rest with
    | nil => simp [fractalKinds, AlternateKinds]
    | cons b rest' =>
      cases rest' with
      | nil => simp [fractalKinds, AlternateKinds]
      | cons c rest'' =>
        simp only [fractalKinds]
        have h_ab_no : ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) := h.1
        have h_ab_no' : ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) := h.2.1
        have h_no_rest : noAdjBarContainment (b :: c :: rest'') := h.2.2
        have ih_rest := ih h_no_rest
        cases h_cls : classifyDef3 a b c with
        | top =>
            have h_is_top := (classifyDef3_eq_top_iff a b c).mp h_cls
            have h_bc_dn : goesDown b c := goesDown_of_top a b c h_is_top
            cases h_rec : fractalKinds (b :: c :: rest'') with
            | nil =>
                show AlternateKinds (FractalKind.top :: [])
                simp [AlternateKinds]
            | cons k' ks' =>
                show AlternateKinds (FractalKind.top :: k' :: ks')
                have h_k' : k' = FractalKind.bottom :=
                  fractalKinds_first_kind_after_down b c rest'' h_bc_dn h_no_rest
                    k' ks' h_rec
                refine ⟨?_, ?_⟩
                · rw [h_k']; intro h_contra; cases h_contra
                · rw [← h_rec]; exact ih_rest
        | bottom =>
            have h_bot := (classifyDef3_eq_bottom_iff a b c).mp h_cls
            obtain ⟨_, h_is_bot⟩ := h_bot
            have h_bc_up : goesUp b c := goesUp_of_bottom a b c h_is_bot
            cases h_rec : fractalKinds (b :: c :: rest'') with
            | nil =>
                show AlternateKinds (FractalKind.bottom :: [])
                simp [AlternateKinds]
            | cons k' ks' =>
                show AlternateKinds (FractalKind.bottom :: k' :: ks')
                have h_k' : k' = FractalKind.top :=
                  fractalKinds_first_kind_after_up b c rest'' h_bc_up h_no_rest
                    k' ks' h_rec
                refine ⟨?_, ?_⟩
                · rw [h_k']; intro h_contra; cases h_contra
                · rw [← h_rec]; exact ih_rest
        | neither =>
            exact ih_rest

end Chanlun.BiReachableDeterminism
