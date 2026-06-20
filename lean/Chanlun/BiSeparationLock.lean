import Chanlun.StrokeUniqueness

/-! Lock theorem for `chanlun_residua.PRIMS["bi_separation"]` vs the δmin=4 SEPARATION CLAUSE
    inside `Chanlun.StrokeUniqueness.IsValidBi` (Tier B; kernel-scope per residua #666).

    Residua-Scheme: `(>= (abs (- pb pt)) 4)` — the 新笔 ⟺ `|p_b − p_t| ≥ 4` test, the audited
    δmin=4 fix. The lock binds the SCHEME side of the separation clause to its Lean equivalent —
    NOT the full list-structural IsValidBi (that is R4 / `bi_decomposition`). -/

namespace Chanlun.Fractal.BiSeparationLock

open Chanlun

/-- The lock theorem: the residua-Scheme separation predicate `|p_b − p_t| ≥ 4` (encoded in
    Lean as `(pb - pt).natAbs ≥ 4 : Bool`) coincides with the Int-shaped clause
    `4 ≤ |pb - pt|` that the IsValidBi state machine uses at δmin=4. -/
theorem evalL_iff_bi_separation (pt pb : Int) :
    decide ((pb - pt).natAbs ≥ 4) = true ↔ (4 : Int) ≤ (pb - pt).natAbs := by
  constructor
  · intro h
    have := (decide_eq_true_iff (p := (pb - pt).natAbs ≥ 4)).mp h
    -- (pb-pt).natAbs : Nat ≥ 4 : Nat  ↔  ((pb-pt).natAbs : Int) ≥ 4 : Int
    omega
  · intro h
    have : (pb - pt).natAbs ≥ 4 := by omega
    exact (decide_eq_true_iff (p := (pb - pt).natAbs ≥ 4)).mpr this

/-- §40 anti-vacuity at the residua-Scheme env (pt=0, pb=4): `|4-0|=4 ≥ 4` ⇒ TRUE; the audited
    δmin=4 boundary is the lock. -/
example : (4 : Int) ≤ ((4 : Int) - 0).natAbs := by decide

end Chanlun.Fractal.BiSeparationLock
