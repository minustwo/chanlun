import Chanlun.Fractal

/-! Lock theorem for `chanlun_residua.PRIMS["inclusion_normalized"]` vs
    `Chanlun.Fractal.isInclusionNormalized` (Tier B).

    The 包含关系 precondition: NONE of the four pairwise inclusion cases hold across the 3-bar
    window. Same `decide` ↔ Prop bridge shape as the other Tier-B locks. -/

namespace Chanlun.Fractal.InclusionNormalizedLock

open Chanlun.Fractal

theorem evalL_iff_isInclusionNormalized (a b c : Bar) :
    decide (¬ (a.h ≤ b.h ∧ a.l ≥ b.l) ∧ ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) ∧
            ¬ (c.h ≤ b.h ∧ c.l ≥ b.l) ∧ ¬ (b.h ≤ c.h ∧ b.l ≥ c.l)) = true
      ↔ isInclusionNormalized a b c := by
  unfold isInclusionNormalized
  exact decide_eq_true_iff

end Chanlun.Fractal.InclusionNormalizedLock
