import Chanlun.StrokeUniqueness
import Chanlun.StrokesIsValidBiCorollary

/-! Lock theorem for `chanlun_residua.PRIMS["bi_decomposition"]` vs
    `Chanlun.StrokeUniqueness.IsValidBi` (R4 closure, Tier B — full list-structural validity).

    The residua-Scheme `bi_decomposition` is a fold over `List Fractal` carrying the
    `⟨anchor, out⟩` `StrokeState` and the 3-branch `Stroke.step` at δmin=4; its evalL output is
    `strokes frs 4` (the unique 笔 list per `strokes_unique`).

    The R4 lock theorem (per Klaus #668): `IsValidBi frs 4 (evalL prog) → strokes_unique ⇒
    唯一分解` — bound here to the existing `strokes_isValidBi` + `strokes_unique` pair, which
    together prove the FULL DETERMINACY VERDICT (`strokes_iff_IsValidBi`): the canonical `strokes
    frs 4` IS the unique IsValidBi witness. The residua-Scheme's content-q discharge claims (by
    construction in `chanlun_residua._BI_DECOMPOSITION`) that evalL computes EXACTLY this
    function — the lake side of that claim is the theorem below. -/

namespace Chanlun.BiDecompositionLock

open Chanlun Chanlun.Stroke Chanlun.StrokeUniqueness Chanlun.StrokesIsValidBiCorollary

/-- The LOCK THEOREM (R4 closure): the canonical `strokes frs 4 : List Stroke` IS the unique
    `IsValidBi` witness at δmin=4 — combining `strokes_isValidBi` (canonicity, this corollary
    file) and `strokes_unique` (uniqueness, `StrokeUniqueness`). The residua-Scheme
    `bi_decomposition` fold is content-q-bound to compute exactly this `strokes frs 4`; that this
    Lean-side function IS the unique validity witness is the discharged lock. -/
theorem strokes_unique_isValidBi_at_4 (frs : List Fractal) :
    IsValidBi frs 4 (strokes frs 4) ∧
    ∀ alt, IsValidBi frs 4 alt → alt = strokes frs 4 := by
  refine ⟨strokes_isValidBi frs 4, ?_⟩
  intro alt h
  exact strokes_unique frs 4 alt h

/-- Bidirectional form (the `strokes_iff_IsValidBi` combined corollary specialized at δmin=4),
    re-exported under the lock namespace as the most ergonomic discharge handle:
    a `List Stroke` validates the 笔 decomposition iff it IS the canonical `strokes` output. -/
theorem evalL_iff_isValidBi_at_4 (frs : List Fractal) (alt : List Stroke) :
    alt = strokes frs 4 ↔ IsValidBi frs 4 alt := by
  exact strokes_iff_IsValidBi frs 4 alt

end Chanlun.BiDecompositionLock
