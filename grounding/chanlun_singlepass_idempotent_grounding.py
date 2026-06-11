"""SINGLE-PASS ≡ FULL-COLLAPSE — the 缠论 包含处理 single-pass normalize is IDEMPOTENT (host anchor).

`chanlun_inclusion_grounding.py` grounded that the single-pass `normalize` (push_one: merge the top pair
once per append) faithfully detects containment + applies the directional merge. It explicitly left OPEN
`[chanlun_norm_singlepass_lean_OPEN]`: is single-pass ≡ full-collapse? (Could a left-to-right pass that
only ever merges the most-recent pair leave a residual containment a full repeated-collapse would catch?)

This harness SETTLES the empirical side: over random integer-interval sequences, the single-pass result
stack NEVER contains an adjacent pair in a containment relation. Therefore a second collapse pass is a
no-op — single-pass already reaches the fixpoint (idempotent), so single-pass ≡ full-collapse. This is
the empirical anchor for the Lean proof (the [cc]/lean dispatch): the load-bearing INVARIANT to prove is

    normalize_no_adjacent_containment :
        ∀ xs, ∀ i < len(normalize xs) - 1, ¬ contained(normalize(xs)[i], normalize(xs)[i+1])

with the key lemma that the directional merge (up ⇒ [max,max], down ⇒ [min,min]) moves the merged top
MONOTONICALLY in the trend direction — away from the lower neighbour — so it cannot create a new
containment with the element below it. The `else` branch only pushes a non-contained item, so freshly
adjacent pushed pairs are non-contained by construction; the only risk is a merge creating a containment
BELOW, which the monotone-direction lemma rules out.

§15 (the harness CAN fail): a deliberately broken normalize that NEVER merges (pushes on containment)
MUST leave a residual adjacent containment — proving the check actually distinguishes collapsed from
un-collapsed. The witness search also asserts the population is non-trivial (sequences that DO trigger
merges are generated), else the ∀ is vacuous.

interp/evalL/evalr are not needed here: this grounds the COMBINATORIAL fixpoint property of N over the
integer-interval algebra (the same `normalize_N` oracle the inclusion grounding sealed against Residua's
`normalize`). The Lean proof is over that same algebra.
"""
from __future__ import annotations

import importlib.util
import random
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent


def _load_inclusion():
    """Reuse the SEALED Algorithm-N primitives (_gen / _contained / _merge / normalize_N) without
    re-deriving them — the inclusion grounding already pins them against Residua's normalize."""
    spec = importlib.util.spec_from_file_location(
        "chanlun_inclusion_grounding", _HERE / "chanlun_inclusion_grounding.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _residual_containments(stack, contained) -> list:
    """Adjacent indices i where stack[i] and stack[i+1] are in a containment relation (would be merged
    by a further collapse pass). EMPTY ⇒ the stack is at the full-collapse fixpoint."""
    return [i for i in range(len(stack) - 1) if contained(stack[i], stack[i + 1])]


def _normalize_never_merge(xs, contained):
    """The §15 MUTANT: a 'normalize' that pushes even on containment (never merges). It MUST leave
    residual containments whenever the input has any — distinguishing collapsed from un-collapsed."""
    return [{"l": it["l"], "h": it["h"]} for it in xs]


def run(n: int, seed: int, M) -> tuple[int, int]:
    """Assert single-pass normalize leaves NO adjacent containment. Returns (checked, merge_triggering)
    where the second counts inputs that actually exercised a merge (non-vacuity)."""
    rng = random.Random(seed)
    merge_triggering = 0
    for i in range(n):
        xs = M._gen(rng)
        stack = M.normalize_N(xs)
        if len(stack) < len(xs):
            merge_triggering += 1                      # a merge collapsed at least one item
        rc = _residual_containments(stack, M._contained)
        if rc:
            raise AssertionError(
                f"[singlepass seed={seed} i={i}] single-pass left a RESIDUAL adjacent containment at "
                f"index {rc[0]} — single-pass ≠ full-collapse.\n  in   ={xs}\n  1pass={stack}")
    return n, merge_triggering


def _self_test(M) -> None:
    # §15: the never-merge mutant MUST leave a residual containment on a containment-bearing input.
    bearing = [{"l": 0, "h": 10}, {"l": 2, "h": 8}]    # second ⊆ first
    assert _residual_containments(_normalize_never_merge(bearing, M._contained), M._contained), \
        "SELF-TEST FAILED (§15): the never-merge mutant did not leave a residual containment — the "
    # ...and the real normalize collapses that same input to no residual containment.
    assert not _residual_containments(M.normalize_N(bearing), M._contained), \
        "SELF-TEST FAILED: normalize_N left a containment on a trivially-collapsible input."


def main() -> int:
    M = _load_inclusion()
    _self_test(M)
    total = triggering = 0
    for seed in (101, 202, 303, 404):
        t, mt = run(60000, seed=seed, M=M)
        total += t
        triggering += mt
    assert triggering >= total // 20, (
        f"non-vacuity too thin: only {triggering}/{total} inputs triggered a merge — the ∀ would be "
        f"near-vacuous; widen the generator.")
    print(f"chanlun_singlepass_idempotent OK: over {total} random integer-interval sequences "
          f"({triggering} of which actually triggered a containment-merge), the single-pass 缠论 "
          f"normalize stack NEVER has an adjacent containment ⇒ a second collapse pass is a no-op ⇒ "
          f"single-pass ≡ full-collapse (normalize is IDEMPOTENT). Empirical anchor for the Lean proof "
          f"[chanlun_norm_singlepass_lean_OPEN]: prove normalize_no_adjacent_containment via the "
          f"monotone-direction merge lemma. §15: the never-merge mutant leaves a residual containment.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
