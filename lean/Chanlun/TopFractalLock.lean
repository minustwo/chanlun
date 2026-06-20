import Chanlun.Fractal

/-! Lock theorem for `chanlun_residua.PRIMS["top_fractal"]` vs `Chanlun.Fractal.isTopFractal`
    (Tier B — cross-domain proof, residua #666 / chanlun #22).

    Residua-Scheme: a 3-bar window predicate `(and (> b.h a.h) (> b.h c.h) (> b.l a.l) (> b.l c.l))`.
    Lean Prop: `isTopFractal a b c := b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l`.
    The lock theorem is the `decide` ↔ `isTopFractal` bridge — same shape as cc's umos-nq Tier-B
    locks (PremiumLock / DiscountLock / ExternalBSLLock / …).
-/

namespace Chanlun.Fractal.TopFractalLock

open Chanlun.Fractal

theorem evalL_iff_isTopFractal (a b c : Bar) :
    decide (b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l) = true ↔ isTopFractal a b c := by
  unfold isTopFractal
  exact decide_eq_true_iff

end Chanlun.Fractal.TopFractalLock
