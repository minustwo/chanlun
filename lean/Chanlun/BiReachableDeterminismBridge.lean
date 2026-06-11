/-
  Chanlun/BiReachableDeterminismBridge.lean

  缠论 Bar↔Interval bridge — the PLUMBING half. Closes
  `[chanlun_bi_reachable_determinism_bridge_OPEN]` (Klaus dispatch on
  #1081 2026-06-11, P6 of the parallel-cc round; the follow-up Klaus
  noted in PR #1098's "Honest scope" as the bridge step).

  ## What this closes

  PR #1083's `ChanlunNormalizeSinglepassIdempotentMWE` proves the
  post-`normalize` invariant at the INTERVAL level:

      normalize_no_adjacent_containment :
          noAdjContainment (normalize xs).1

  PR #1098's `ChanlunBiReachableDeterminismMWE` proves the Bar-level
  alternation theorem:

      fractals_alternate_on_containment_free :
          noAdjBarContainment bars → AlternateKinds (fractalKinds bars)

  These two are at different levels — `Interval` vs `Bar` — and the
  Bar↔Interval converter `toBar` lives in PR #1083's
  `ChanlunPipelineCompositionMWE`. PR #1098's "Honest scope" §1
  explicitly notes the bridge as straightforward per-pair plumbing left
  as a follow-up. THIS MWE supplies it.

  ## Proof structure

  Two theorems:

  1. **`map_toBar_preserves_noAdjContainment`** — the per-pair bridge:
     for any `Interval` list satisfying `noAdjContainment`, the mapped
     `Bar` list satisfies `noAdjBarContainment`. By induction over the
     list; each `a :: b :: rest` step decomposes `noAdjContainment`'s
     `¬ contained a b` into the two Bar-level negations via
     `not_contained_iff_bar` (PR #1083 pipeline composition).

  2. **`normalize_then_fractals_alternate`** — the user-facing corollary:
     chaining `normalize_no_adjacent_containment` →
     `map_toBar_preserves_noAdjContainment` →
     `fractals_alternate_on_containment_free`, so any RAW input list
     `xs : List Interval`, after `normalize` + `toBar`, has its Def-3
     fractal-kind sequence strictly alternating — the user-facing form
     of the 缠论 唯一分解 verdict on the reachable domain.

  ## Honest scope

  This is the pure plumbing — both halves are already proven in their
  respective MWEs (PR #1083 + PR #1098); the bridge just composes them.
  No new mathematical content; the value is enabling downstream
  one-step rewrites from raw `Interval` lists to the alternation
  conclusion (instead of users having to re-prove the bridge each time).
-/

import Mathlib.Tactic
import Chanlun.BiReachableDeterminism
import Chanlun.Pipeline
import Chanlun.Normalize

namespace Chanlun.BiReachableDeterminismBridge

open Chanlun.BiReachableDeterminism
open Chanlun.Pipeline
open Chanlun.Normalize

/-! ## §1 — The per-pair bridge lemma. -/

/-- THE BRIDGE LEMMA. The Interval-level `noAdjContainment` (PR #1083's
    post-`normalize` invariant) lifts to the Bar-level
    `noAdjBarContainment` (PR #1098's alternation premise) via the per-
    pair `not_contained_iff_bar` converter (PR #1083 pipeline).

    By induction over the list. The `a :: b :: rest` case unfolds
    `noAdjContainment` to `¬ contained a b ∧ noAdjContainment (b :: rest)`,
    applies `not_contained_iff_bar` to get the two Bar-level negations,
    and recurses. The shorter cases (`[]`, `[_]`) are trivial. -/
theorem map_toBar_preserves_noAdjContainment :
    ∀ xs : List Interval,
      noAdjContainment xs → noAdjBarContainment (xs.map toBar) := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp [List.map, noAdjBarContainment]
  | cons a rest ih =>
      intro h
      cases rest with
      | nil =>
          simp [List.map, noAdjBarContainment]
      | cons b rest' =>
          -- h : noAdjContainment (a :: b :: rest')
          --   = ¬ contained a b ∧ noAdjContainment (b :: rest')
          unfold noAdjContainment at h
          obtain ⟨h_nc, h_rest⟩ := h
          have h_bar := (not_contained_iff_bar a b).mp h_nc
          -- h_bar : ¬ ((toBar a).h ≤ (toBar b).h ∧ (toBar a).l ≥ (toBar b).l) ∧
          --         ¬ ((toBar b).h ≤ (toBar a).h ∧ (toBar b).l ≥ (toBar a).l)
          have ih_rest := ih h_rest
          -- ih_rest : noAdjBarContainment ((b :: rest').map toBar)
          --        = noAdjBarContainment (toBar b :: rest'.map toBar)
          -- Goal: noAdjBarContainment ((a :: b :: rest').map toBar)
          --     = noAdjBarContainment (toBar a :: toBar b :: rest'.map toBar)
          simp only [List.map]
          unfold noAdjBarContainment
          refine ⟨h_bar.1, h_bar.2, ?_⟩
          -- Goal: noAdjBarContainment (toBar b :: rest'.map toBar)
          -- Have: ih_rest : noAdjBarContainment (toBar b :: rest'.map toBar)
          simp only [List.map] at ih_rest
          exact ih_rest

/-! ## §2 — THE USER-FACING COROLLARY. -/

/-- **THE USER-FACING COROLLARY** (Klaus's named P6 target). Chaining
    PR #1083's `normalize_no_adjacent_containment` with this MWE's
    bridge with PR #1098's `fractals_alternate_on_containment_free`:
    for ANY raw input `xs : List Interval`, after `normalize` + `toBar`
    + `fractalKinds`, the resulting fractal-kind sequence ALTERNATES.

    This is the one-line user-facing form: raw input → alternation
    verdict, no intermediate plumbing visible. -/
theorem normalize_then_fractals_alternate :
    ∀ xs : List Interval,
      AlternateKinds (fractalKinds ((normalize xs).1.map toBar)) := by
  intro xs
  have h_nac : noAdjContainment (normalize xs).1 :=
    normalize_no_adjacent_containment xs
  have h_bar_nac : noAdjBarContainment ((normalize xs).1.map toBar) :=
    map_toBar_preserves_noAdjContainment (normalize xs).1 h_nac
  exact fractals_alternate_on_containment_free ((normalize xs).1.map toBar) h_bar_nac

end Chanlun.BiReachableDeterminismBridge
