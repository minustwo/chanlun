import Chanlun.Fractal

/-! Lock theorem for `chanlun_residua.PRIMS["bottom_fractal"]` vs `Chanlun.Fractal.isBottomFractal`
    (Tier B). Mirror of `TopFractalLock` with reversed inequalities. -/

namespace Chanlun.Fractal.BottomFractalLock

open Chanlun.Fractal

theorem evalL_iff_isBottomFractal (a b c : Bar) :
    decide (b.l < a.l ∧ b.l < c.l ∧ b.h < a.h ∧ b.h < c.h) = true ↔ isBottomFractal a b c := by
  unfold isBottomFractal
  exact decide_eq_true_iff

end Chanlun.Fractal.BottomFractalLock
