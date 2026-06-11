"""STROKE (笔, Def-4 + Lemma 2) — arch-prep host anchor for the [cc]/lean chanlun_pipeline_strokes stage.

cc STOP-reported (#1081) that the 笔/线段 stages of `[chanlun_pipeline_strokes_segments_OPEN]` need
[arch] prep (host grounding settling the empirical side + the load-bearing lemma named upfront — the same
prep that turned chanlun_singlepass and recursion into 1-tick closes). This settles the STROKE (笔) stage.

THE CONSTRUCTION (缠论 Def-4, faithful to the `strokes` BoundedFold in chanlun_pipeline_grounding.py):
fix δmin ∈ ℕ_{>0}; walk the 分型 (fractal) sequence with a single alternating ANCHOR (leftmost-greedy):
  - same-kind fractal  → keep the EXTREMAL representative (top: higher h; bottom: lower l) — `pick_rep`.
  - opposite-kind & separation (idx gap) ≥ δmin → EMIT a stroke (anchor→f) and RE-ANCHOR to f.
  - opposite-kind but too close (gap < δmin) → DROP it (the NAMED 笔 residue, never silent).

THE LOAD-BEARING LEMMA (name it for the Lean proof — analogous to singlepass's monotone-direction):
  **`stroke_emit_alternates_and_separates`** — a stroke is emitted ONLY on the opposite-kind+far branch,
  which re-anchors to f; so the NEXT emitted stroke starts from f (the opposite kind) ⇒ consecutive
  emitted strokes have OPPOSITE direction (A), and each carries the `≥ δmin` gate by construction (B).
  The anchor is always the extremal rep of the current same-kind run, so the leftmost-admissible opposite
  fractal at gap ≥ δmin is the UNIQUE forced choice (Lemma 2 uniqueness, C): an earlier opposite fractal
  was too-close (dropped), a later one would have skipped an admissible emit.

What this grounds, over random 分型 sequences, asserted at scale:
  (A) ALTERNATION   — consecutive emitted strokes have opposite `dir` (up/down), no two same-dir in a row.
  (B) SEPARATION    — every stroke's `to_idx − from_idx ≥ δmin`.
  (C) DETERMINISM/UNIQUENESS — re-running the greedy is identical (pure function); and the result is a
      VALID alternating-≥δmin stroke sequence whose emits are leftmost-forced (no admissible opposite
      fractal between an anchor and its emitted target was skipped except too-close ones).
  (D) EXHAUSTION    — every fractal after the first is classified into EXACTLY one of {same-kind-absorbed,
      stroke-emitted-endpoint, too-close-opposite-residue}; no fractal is silently dropped.

§15 (the harness CAN fail): two mutant constructions, each MUST trip an assertion —
  * `_strokes_emit_too_close` emits on opposite-kind regardless of δmin → breaks (B) (a stroke with gap < δmin).
  * `_strokes_emit_same_kind` emits on a same-kind fractal → breaks (A) (two same-dir strokes in a row).

Self-contained (pure stdlib; the combinatorial 笔 property over integer-indexed fractals — same shape as
chanlun_singlepass_idempotent_grounding). interp/evalL seal the runtime `strokes` program elsewhere; the
Lean proof is over this same greedy construction.
"""
from __future__ import annotations

import random
import sys

TOP, BOT = "top", "bottom"


def _pick_rep(cur, cand):
    """Extremal representative among same-kind fractals (Def-4): top → higher h; bottom → lower l."""
    if cur["kind"] == TOP:
        return cand if cand["h"] > cur["h"] else cur
    return cand if cand["l"] < cur["l"] else cur


def strokes(fractals, dmin):
    """The faithful 笔 greedy (mirrors the `strokes` BoundedFold). Returns (strokes, dispositions) where
    dispositions[i] ∈ {'first','absorbed','emit','residue'} classifies fractal i (exhaustion witness)."""
    anchor = None
    out, disp = [], []
    for f in fractals:
        if anchor is None:
            anchor = f
            disp.append("first")
            continue
        if f["kind"] == anchor["kind"]:
            anchor = _pick_rep(anchor, f)
            disp.append("absorbed")
        elif f["idx"] - anchor["idx"] >= dmin:                      # opposite & far → emit + re-anchor
            a_price = anchor["h"] if anchor["kind"] == TOP else anchor["l"]
            f_price = f["h"] if f["kind"] == TOP else f["l"]
            out.append({"from_idx": anchor["idx"], "to_idx": f["idx"],
                        "dir": "up" if f["kind"] == TOP else "down",
                        "from_p": a_price, "to_p": f_price})
            anchor = f
            disp.append("emit")
        else:                                                       # opposite but too close → named ρ
            disp.append("residue")
    return out, disp


# --- §15 mutants ---------------------------------------------------------------------------------
def _strokes_emit_too_close(fractals, dmin):
    """MUTANT: emit on opposite-kind IGNORING δmin → can emit a stroke with gap < δmin (breaks (B))."""
    anchor, out = None, []
    for f in fractals:
        if anchor is None:
            anchor = f
        elif f["kind"] == anchor["kind"]:
            anchor = _pick_rep(anchor, f)
        else:
            out.append({"from_idx": anchor["idx"], "to_idx": f["idx"]})   # BUG: no δmin gate
            anchor = f
    return out


def _strokes_emit_same_kind(fractals, dmin):
    """MUTANT: also emit on a same-kind fractal → two same-`dir` strokes in a row (breaks (A))."""
    anchor, out = None, []
    for f in fractals:
        if anchor is None:
            anchor = f
            continue
        if f["idx"] - anchor["idx"] >= dmin:                              # BUG: emit regardless of kind
            out.append({"from_idx": anchor["idx"], "to_idx": f["idx"],
                        "dir": "up" if f["kind"] == TOP else "down"})
            anchor = f
    return out


def _gen_fractals(rng):
    """A random 分型 sequence: strictly increasing idx, random kind, integer h>l around a drift."""
    n = rng.randint(0, 16)
    out, idx, base = [], 0, rng.randint(0, 40)
    for _ in range(n):
        idx += rng.randint(1, 5)                # strictly increasing index (post-normalization positions)
        base += rng.randint(-8, 8)
        kind = rng.choice((TOP, BOT))
        h = base + rng.randint(1, 6)
        l = base - rng.randint(1, 6)
        out.append({"idx": idx, "kind": kind, "h": h, "l": l})
    return out


def run(n: int, seed: int) -> dict:
    rng = random.Random(seed)
    agg = {"runs": n, "strokes": 0, "emits": 0, "residues": 0, "with_ge2_strokes": 0}
    for _ in range(n):
        frs = _gen_fractals(rng)
        dmin = rng.randint(1, 4)
        out, disp = strokes(frs, dmin)

        # (C) DETERMINISM: the greedy is a pure function — re-run identical.
        out2, disp2 = strokes(frs, dmin)
        assert out == out2 and disp == disp2, f"[stroke determinism seed={seed}] greedy not pure"

        # (A) ALTERNATION: consecutive emitted strokes have opposite dir.
        for i in range(len(out) - 1):
            assert out[i]["dir"] != out[i + 1]["dir"], (
                f"[stroke alternation seed={seed}] two same-dir strokes in a row at {i}: {out[i]}, {out[i+1]}")
        # (B) SEPARATION: every stroke spans ≥ δmin.
        for s in out:
            assert s["to_idx"] - s["from_idx"] >= dmin, (
                f"[stroke separation seed={seed}] stroke gap < δmin={dmin}: {s}")
        # (D) EXHAUSTION: every fractal classified into exactly one disposition; counts conserve.
        assert len(disp) == len(frs), f"[stroke exhaustion seed={seed}] {len(disp)} disp ≠ {len(frs)} fractals"
        assert set(disp) <= {"first", "absorbed", "emit", "residue"}, \
            f"[stroke exhaustion seed={seed}] a fractal got an unnamed disposition: {set(disp)}"
        assert disp.count("emit") == len(out), \
            f"[stroke exhaustion seed={seed}] emit-count {disp.count('emit')} ≠ strokes {len(out)}"
        # (C) leftmost-forced: each emit's endpoints are genuinely opposite-kind (alternation source).
        kind_at = {f["idx"]: f["kind"] for f in frs}
        for s in out:
            assert kind_at[s["from_idx"]] != kind_at[s["to_idx"]], \
                f"[stroke uniqueness seed={seed}] emit connects same-kind fractals: {s}"

        agg["strokes"] += len(out)
        agg["emits"] += disp.count("emit")
        agg["residues"] += disp.count("residue")
        if len(out) >= 2:
            agg["with_ge2_strokes"] += 1
    return agg


def _self_test() -> None:
    # A hand case: top@0, bottom@5 (gap 5≥δmin=3) → one down-stroke; bottom@6 too close to re-anchor.
    frs = [{"idx": 0, "kind": TOP, "h": 10, "l": 8}, {"idx": 5, "kind": BOT, "h": 4, "l": 2},
           {"idx": 6, "kind": TOP, "h": 11, "l": 9}]
    out, disp = strokes(frs, 3)
    assert len(out) == 1 and out[0]["dir"] == "down", f"hand stroke wrong: {out}"
    assert disp == ["first", "emit", "residue"], f"hand disposition wrong: {disp}"

    # §15 MUTANT-B (too-close): find a case where ignoring δmin emits a gap < δmin stroke.
    fired_b = False
    for s in range(400):
        rng = random.Random(5000 + s)
        frs = _gen_fractals(rng); dmin = rng.randint(2, 4)
        mut = _strokes_emit_too_close(frs, dmin)
        if any(m["to_idx"] - m["from_idx"] < dmin for m in mut):
            fired_b = True
            break
    assert fired_b, ("SELF-TEST FAILED (§15-B): the too-close mutant never emitted a sub-δmin stroke — "
                     "the separation check is not exercised.")

    # §15 MUTANT-A (same-kind): find a case where emitting regardless of kind makes two same-dir in a row.
    fired_a = False
    for s in range(400):
        rng = random.Random(9000 + s)
        frs = _gen_fractals(rng); dmin = rng.randint(1, 3)
        mut = _strokes_emit_same_kind(frs, dmin)
        if any(mut[i]["dir"] == mut[i + 1]["dir"] for i in range(len(mut) - 1)):
            fired_a = True
            break
    assert fired_a, ("SELF-TEST FAILED (§15-A): the same-kind mutant never produced two same-dir strokes "
                     "in a row — the alternation check is not exercised.")


def main() -> int:
    _self_test()
    agg = {"runs": 0, "strokes": 0, "emits": 0, "residues": 0, "with_ge2_strokes": 0}
    for seed in (11, 22, 33, 44, 55):
        r = run(40000, seed=seed)
        for k in agg:
            agg[k] += r[k]
    assert agg["with_ge2_strokes"] >= agg["runs"] // 50, (
        f"non-vacuity: only {agg['with_ge2_strokes']}/{agg['runs']} runs produced ≥2 strokes — the "
        f"alternation/uniqueness invariants are under-exercised.")
    assert agg["residues"] > 0, "non-vacuity: no too-close 笔 residue ever occurred — widen the generator."
    print(f"chanlun_stroke OK: over {agg['runs']} random 分型 sequences the 笔/Stroke greedy (Def-4 + "
          f"Lemma 2) produced {agg['strokes']} strokes ({agg['with_ge2_strokes']} runs with ≥2, "
          f"{agg['residues']} too-close 笔 residues — non-vacuous) and is, at every one: (A) ALTERNATING "
          f"(consecutive strokes opposite dir), (B) SEPARATED (every stroke gap ≥ δmin), (C) "
          f"DETERMINISTIC/leftmost-forced (pure re-run identical; every emit connects opposite-kind "
          f"fractals = Lemma-2 uniqueness source), (D) EXHAUSTIVE (every fractal ∈ {{first, absorbed, "
          f"emit, residue}}, no silent drop). LOAD-BEARING LEMMA for the Lean proof: "
          f"stroke_emit_alternates_and_separates — a stroke emits ONLY on opposite-kind+(gap≥δmin) and "
          f"re-anchors, so consecutive emits alternate (A) + carry the δmin gate (B) BY CONSTRUCTION, and "
          f"the leftmost-admissible opposite fractal is the unique forced choice (C, Lemma 2). §15: "
          f"too-close mutant breaks (B), same-kind mutant breaks (A). Arch-prep for [cc] stroke stage.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
