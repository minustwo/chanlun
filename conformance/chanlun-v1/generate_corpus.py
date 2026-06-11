"""Generator for the `chanlun-v1` conformance corpus.

Running this script produces a deterministic set of (input -> expected-output) JSON fixtures
plus the top-level `manifest.json`. The contract: re-running this script on the same Python /
on any byte-identical reference backend produces byte-identical fixture JSON and byte-identical
`manifest.json`. That byte equality is what FREEZES the spec.

Pure stdlib only (no numpy / pandas) - so the corpus is portable across languages.

The fixtures cover each stage in isolation + the full pipeline, over a mix of:

    *  Hand cases   - small, named, each exercising a specific invariant
    *  Synthetic    - deterministic random K-line series (seeded), end-to-end pipeline
    *  Stage-only   - each stage on its own input to make per-stage debugging easy

Categories produced (in the `fixtures/` dir, one file per fixture):

    normalize_*.json     - Algorithm N (Appendix A) stage only
    fractal_*.json       - Def-3 fractal extraction stage only
    stroke_*.json        - Def-4 + Lemma 2 stroke greedy stage only
    zhongshu_*.json      - Center construction stage only
    trend_type_*.json    - Trend-type classification stage only
    pipeline_*.json      - End-to-end (bars -> trend type)

Each fixture file has the wire shape:

    {
      "id":        "stage.name",
      "stage":     "normalize" | "fractal" | "stroke" | "zhongshu" | "trend_type" | "pipeline",
      "input":     <canonical-JSON of the inputs to the stage>,
      "expected":  <canonical-JSON of the expected outputs>,
      "input_sha256":    "<sha>",
      "expected_sha256": "<sha>",
      "fixture_sha256":  "<sha over the canonical concat>"
    }

The runner reproduces `expected` by running `reference_backend` on `input` and asserts
`fixture_sha256` byte-for-byte against the manifest.
"""
from __future__ import annotations

import hashlib
import json
import random
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent.parent))     # so `from conformance.chanlun_v1.reference_backend...` works
sys.path.insert(0, str(_HERE))                    # so `from reference_backend ...` works

from reference_backend import pipeline as P  # noqa: E402
from reference_backend import normalize as Nmod  # noqa: E402
from reference_backend import fractal as Fmod  # noqa: E402
from reference_backend import strokes as Smod  # noqa: E402
from reference_backend import zhongshu as Zmod  # noqa: E402
from reference_backend import trend_type as Tmod  # noqa: E402


CORPUS_VERSION = "chanlun-v1"
FIXTURES_DIR = _HERE / "fixtures"
MANIFEST_PATH = _HERE / "manifest.json"

# Canonical-JSON: sort_keys=True, indent=None, separators=(",",":"), ensure_ascii=True.
# Every fixture file is then pretty-printed for readability, but the SHA is over the canonical form.
_CANON_KW = dict(sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def canon(obj) -> bytes:
    """Canonical-JSON bytes used for ALL SHA-256 computation. Deterministic and byte-stable."""
    return json.dumps(obj, **_CANON_KW).encode("utf-8")


def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


# ---------------------------------------------------------------------------
# Bar generators (deterministic).
# ---------------------------------------------------------------------------

def gen_walk_bars(seed: int, n: int, start: int = 100, step_range: int = 5, half_range: int = 6):
    """A random-walk K-line series. Each bar drifts from the previous mid by `step_range`; `half_range`
    is the half-spread. Integer-only. Length `n`, seeded for determinism."""
    rng = random.Random(seed)
    out = []
    mid = start
    for _ in range(n):
        mid += rng.randint(-step_range, step_range)
        half = rng.randint(1, half_range)
        out.append({"l": mid - half, "h": mid + half})
    return out


def gen_trending_bars(seed: int, n: int, direction: int = +1, start: int = 100, drift: int = 3, jitter: int = 2):
    """A directional K-line series (drift dominates jitter) so that the pipeline produces a 趋势."""
    rng = random.Random(seed)
    out, mid = [], start
    for _ in range(n):
        mid += direction * drift + rng.randint(-jitter, jitter)
        half = rng.randint(1, 4)
        out.append({"l": mid - half, "h": mid + half})
    return out


# ---------------------------------------------------------------------------
# Hand cases (named).
# ---------------------------------------------------------------------------

HAND_NORMALIZE = [
    ("normalize.hand_single_containment",
     "Two bars in containment collapse to one merged interval (up-rule).",
     [{"l": 0, "h": 10}, {"l": 2, "h": 8}]),
    ("normalize.hand_no_containment",
     "Two adjacent non-contained bars pass through unchanged.",
     [{"l": 0, "h": 5}, {"l": 6, "h": 10}]),
    ("normalize.hand_chain_collapse",
     "Chain of nested intervals collapses left-to-right.",
     [{"l": 0, "h": 10}, {"l": 2, "h": 8}, {"l": 3, "h": 7}, {"l": 4, "h": 6}]),
    ("normalize.hand_empty",
     "Empty input -> empty stack.",
     []),
    ("normalize.hand_single",
     "Single bar -> single-element stack.",
     [{"l": 5, "h": 7}]),
    ("normalize.hand_down_merge",
     "Down-direction containment: after a higher prior bar, the contained pair uses min/min.",
     [{"l": 5, "h": 10}, {"l": 7, "h": 9}, {"l": 0, "h": 4}, {"l": 1, "h": 3}]),
]

HAND_FRACTAL = [
    ("fractal.hand_top",
     "A 3-bar window with the middle strictly above both neighbours -> top.",
     [{"l": 5, "h": 10}, {"l": 8, "h": 15}, {"l": 6, "h": 12}]),
    ("fractal.hand_bottom",
     "A 3-bar window with the middle strictly below both neighbours -> bottom.",
     [{"l": 5, "h": 10}, {"l": 2, "h": 6}, {"l": 4, "h": 9}]),
    ("fractal.hand_neither",
     "A flat-ish 3-bar window with no extremum -> neither (dropped).",
     [{"l": 5, "h": 10}, {"l": 6, "h": 11}, {"l": 7, "h": 12}]),
    ("fractal.hand_two_fractals",
     "5-bar window: top at idx 1, bottom at idx 3 (alternating Def-3).",
     [{"l": 5, "h": 10}, {"l": 8, "h": 15}, {"l": 6, "h": 12}, {"l": 2, "h": 7}, {"l": 5, "h": 11}]),
]

HAND_STROKE = [
    ("stroke.hand_one_down",
     "Top at idx 0, bottom at idx 5 with gap >= dmin=3 -> one down-stroke; a too-close top is residue.",
     {
         "fractals": [
             {"idx": 0, "kind": "top", "h": 10, "l": 8},
             {"idx": 5, "kind": "bottom", "h": 4, "l": 2},
             {"idx": 6, "kind": "top", "h": 11, "l": 9},
         ],
         "dmin": 3,
     }),
    ("stroke.hand_absorbed_same_kind",
     "Two consecutive tops (idx 0, idx 4): the second is absorbed (extremal rep wins).",
     {
         "fractals": [
             {"idx": 0, "kind": "top", "h": 10, "l": 8},
             {"idx": 4, "kind": "top", "h": 12, "l": 9},
             {"idx": 8, "kind": "bottom", "h": 5, "l": 3},
         ],
         "dmin": 3,
     }),
    ("stroke.hand_empty",
     "Empty fractal list -> empty strokes + empty dispositions.",
     {"fractals": [], "dmin": 4}),
]

HAND_ZHONGSHU = [
    ("zhongshu.hand_one_center",
     "Three elements with a shared overlap zone -> one center; fourth element leaves the zone.",
     {
         "elements": [
             {"idx": 0, "lo": 45, "hi": 55},
             {"idx": 1, "lo": 48, "hi": 58},
             {"idx": 2, "lo": 44, "hi": 53},
             {"idx": 3, "lo": 49, "hi": 60},
             {"idx": 4, "lo": 90, "hi": 99},
         ],
         "zone": "first3",
     }),
    ("zhongshu.hand_no_overlap",
     "Three non-overlapping elements -> no center forms.",
     {
         "elements": [
             {"idx": 0, "lo": 0, "hi": 2},
             {"idx": 1, "lo": 10, "hi": 12},
             {"idx": 2, "lo": 20, "hi": 22},
         ],
         "zone": "first3",
     }),
    ("zhongshu.hand_all_zone",
     "Same 5 elements as hand_one_center but with the `all` zone gate (re-tightens to all members).",
     {
         "elements": [
             {"idx": 0, "lo": 45, "hi": 55},
             {"idx": 1, "lo": 48, "hi": 58},
             {"idx": 2, "lo": 44, "hi": 53},
             {"idx": 3, "lo": 49, "hi": 60},
             {"idx": 4, "lo": 90, "hi": 99},
         ],
         "zone": "all",
     }),
]

HAND_TREND_TYPE = [
    ("trend_type.hand_none",
     "Zero centers -> none.",
     []),
    ("trend_type.hand_consolidation",
     "Exactly one center -> consolidation.",
     [{"start": 0, "end": 2, "ZD": 48, "ZG": 53, "n": 3}]),
    ("trend_type.hand_trend_up",
     "Two centers, second strictly above first -> trend_up.",
     [{"start": 0, "end": 2, "ZD": 10, "ZG": 20, "n": 3},
      {"start": 3, "end": 5, "ZD": 30, "ZG": 40, "n": 3}]),
    ("trend_type.hand_trend_down",
     "Two centers, second strictly below first -> trend_down.",
     [{"start": 0, "end": 2, "ZD": 30, "ZG": 40, "n": 3},
      {"start": 3, "end": 5, "ZD": 10, "ZG": 20, "n": 3}]),
    ("trend_type.hand_mixed",
     "Three centers stepping up then overlapping -> mixed (named residue).",
     [{"start": 0, "end": 2, "ZD": 10, "ZG": 20, "n": 3},
      {"start": 3, "end": 5, "ZD": 30, "ZG": 40, "n": 3},
      {"start": 6, "end": 8, "ZD": 35, "ZG": 45, "n": 3}]),
]


# ---------------------------------------------------------------------------
# Building one fixture (any stage).
# ---------------------------------------------------------------------------

def make_fixture(fid: str, stage: str, description: str, inp, expected) -> dict:
    """Construct one fixture dict + the three SHAs (input, expected, fixture)."""
    inp_canon = canon(inp)
    exp_canon = canon(expected)
    in_sha = sha256(inp_canon)
    ex_sha = sha256(exp_canon)
    # `fixture_sha256` is SHA over the canonical concat (delimiter prevents extension attacks).
    fixture_sha = sha256(inp_canon + b"|" + exp_canon)
    return {
        "id": fid,
        "stage": stage,
        "description": description,
        "input": inp,
        "expected": expected,
        "input_sha256": in_sha,
        "expected_sha256": ex_sha,
        "fixture_sha256": fixture_sha,
    }


# ---------------------------------------------------------------------------
# Per-stage runners (the SAME calls the runner.py does at verification time).
# ---------------------------------------------------------------------------

def stage_run_normalize(inp):
    return Nmod.normalize_N(inp)


def stage_run_fractal(inp):
    return Fmod.extract_fractals(inp)


def stage_run_stroke(inp):
    out, disp = Smod.strokes(inp["fractals"], inp["dmin"])
    return {"strokes": out, "dispositions": disp}


def stage_run_zhongshu(inp):
    return Zmod.zhongshu(inp["elements"], inp["zone"])


def stage_run_trend_type(inp):
    return Tmod.classify(inp)


def stage_run_pipeline(inp):
    return P.run_full(inp["bars"], dmin=inp.get("dmin", P.DMIN), zone=inp.get("zone", "first3"))


STAGE_RUNNERS = {
    "normalize":  stage_run_normalize,
    "fractal":    stage_run_fractal,
    "stroke":     stage_run_stroke,
    "zhongshu":   stage_run_zhongshu,
    "trend_type": stage_run_trend_type,
    "pipeline":   stage_run_pipeline,
}


# ---------------------------------------------------------------------------
# Collect all fixtures.
# ---------------------------------------------------------------------------

def collect_fixtures() -> list:
    fxs = []

    # --- HAND CASES (per stage) ----------------------------------------------
    for fid, desc, inp in HAND_NORMALIZE:
        fxs.append(make_fixture(fid, "normalize", desc, inp, stage_run_normalize(inp)))
    for fid, desc, inp in HAND_FRACTAL:
        fxs.append(make_fixture(fid, "fractal", desc, inp, stage_run_fractal(inp)))
    for fid, desc, inp in HAND_STROKE:
        fxs.append(make_fixture(fid, "stroke", desc, inp, stage_run_stroke(inp)))
    for fid, desc, inp in HAND_ZHONGSHU:
        fxs.append(make_fixture(fid, "zhongshu", desc, inp, stage_run_zhongshu(inp)))
    for fid, desc, inp in HAND_TREND_TYPE:
        fxs.append(make_fixture(fid, "trend_type", desc, inp, stage_run_trend_type(inp)))

    # --- SYNTHETIC NORMALIZE FIXTURES (seeded walks of varying lengths) ------
    for seed, n in [(101, 10), (202, 25), (303, 50), (404, 100)]:
        bars = gen_walk_bars(seed, n)
        fxs.append(make_fixture(
            f"normalize.synth_walk_seed{seed}_n{n}",
            "normalize",
            f"Random walk bars (seed={seed}, n={n}) -> Algorithm N normalize stack.",
            bars, stage_run_normalize(bars)))

    # --- SYNTHETIC FRACTAL FIXTURES (normalize then feed into fractal) -------
    for seed, n in [(501, 30), (602, 60), (703, 120)]:
        bars = Nmod.normalize_N(gen_walk_bars(seed, n))
        fxs.append(make_fixture(
            f"fractal.synth_post_norm_seed{seed}_n{n}",
            "fractal",
            f"Post-normalize bars (seed={seed}, n={n}) -> Def-3 fractal sequence.",
            bars, stage_run_fractal(bars)))

    # --- SYNTHETIC STROKE FIXTURES (feed real fractals through) --------------
    for seed, n in [(801, 60), (902, 120), (1003, 240)]:
        bars = Nmod.normalize_N(gen_walk_bars(seed, n))
        frs = Fmod.extract_fractals(bars)
        inp = {"fractals": frs, "dmin": 4}
        fxs.append(make_fixture(
            f"stroke.synth_post_fractal_seed{seed}_n{n}",
            "stroke",
            f"Post-fractal stream (seed={seed}, n={n}) -> Def-4 strokes at dmin=4.",
            inp, stage_run_stroke(inp)))

    # --- SYNTHETIC ZHONGSHU FIXTURES (stroke elements through) ---------------
    for seed, n in [(1101, 120), (1202, 200), (1303, 300)]:
        bars = Nmod.normalize_N(gen_walk_bars(seed, n))
        frs = Fmod.extract_fractals(bars)
        sts, _disp = Smod.strokes(frs, 4)
        elems = P.strokes_to_elements(sts)
        for zone in ("first3", "all"):
            inp = {"elements": elems, "zone": zone}
            fxs.append(make_fixture(
                f"zhongshu.synth_zone_{zone}_seed{seed}_n{n}",
                "zhongshu",
                f"Stroke-elements (seed={seed}, n={n}, zone={zone}) -> center decomposition.",
                inp, stage_run_zhongshu(inp)))

    # --- TREND-TYPE SYNTHETIC FIXTURES (hand-crafted center sequences) -------
    # Pure-trending K-line walks collapse to zero fractals (no local extrema), so trend_type
    # synthetics MUST come from hand-crafted center sequences that exercise each class.
    trend_synth = [
        (
            "trend_type.synth_trend_up_3centers",
            "Three step-up centers -> trend_up (all dirs +1).",
            [{"start": 0, "end": 2, "ZD": 10, "ZG": 20, "n": 3},
             {"start": 3, "end": 5, "ZD": 30, "ZG": 40, "n": 3},
             {"start": 6, "end": 8, "ZD": 50, "ZG": 60, "n": 3}],
        ),
        (
            "trend_type.synth_trend_down_4centers",
            "Four step-down centers -> trend_down (all dirs -1).",
            [{"start": 0, "end": 2, "ZD": 80, "ZG": 95, "n": 3},
             {"start": 3, "end": 5, "ZD": 55, "ZG": 70, "n": 3},
             {"start": 6, "end": 8, "ZD": 30, "ZG": 45, "n": 3},
             {"start": 9, "end": 11, "ZD": 5, "ZG": 20, "n": 3}],
        ),
        (
            "trend_type.synth_mixed_updown",
            "Two centers stepping up then one stepping down -> mixed.",
            [{"start": 0, "end": 2, "ZD": 10, "ZG": 20, "n": 3},
             {"start": 3, "end": 5, "ZD": 30, "ZG": 40, "n": 3},
             {"start": 6, "end": 8, "ZD": 15, "ZG": 25, "n": 3}],
        ),
    ]
    for fid, desc, centers in trend_synth:
        fxs.append(make_fixture(fid, "trend_type", desc, centers, stage_run_trend_type(centers)))

    # --- FULL-PIPELINE FIXTURES (the headline) -------------------------------
    pipeline_specs = [
        ("pipeline.synth_walk_seed3001_n40",   "Random walk K-lines (seed=3001, n=40), default dmin/zone.",
         gen_walk_bars(3001, 40), 4, "first3"),
        ("pipeline.synth_walk_seed3002_n80",   "Random walk K-lines (seed=3002, n=80), default dmin/zone.",
         gen_walk_bars(3002, 80), 4, "first3"),
        ("pipeline.synth_walk_seed3003_n160",  "Random walk K-lines (seed=3003, n=160), default dmin/zone.",
         gen_walk_bars(3003, 160), 4, "first3"),
        ("pipeline.synth_walk_seed3004_n320",  "Random walk K-lines (seed=3004, n=320), default dmin/zone.",
         gen_walk_bars(3004, 320), 4, "first3"),
        ("pipeline.synth_up_seed3101_n100",    "Up-trending K-lines (seed=3101, n=100).",
         gen_trending_bars(3101, 100, +1), 4, "first3"),
        ("pipeline.synth_down_seed3201_n100",  "Down-trending K-lines (seed=3201, n=100).",
         gen_trending_bars(3201, 100, -1), 4, "first3"),
        ("pipeline.synth_walk_seed3301_n80_zone_all",
         "Random walk K-lines (seed=3301, n=80), `all` zone gate.",
         gen_walk_bars(3301, 80), 4, "all"),
        ("pipeline.synth_walk_seed3401_n80_dmin2",
         "Random walk K-lines (seed=3401, n=80), dmin=2 (laxer stroke gate).",
         gen_walk_bars(3401, 80), 2, "first3"),
    ]
    for fid, desc, bars, dmin, zone in pipeline_specs:
        inp = {"bars": bars, "dmin": dmin, "zone": zone}
        fxs.append(make_fixture(fid, "pipeline", desc, inp, stage_run_pipeline(inp)))

    return fxs


# ---------------------------------------------------------------------------
# Write fixtures + manifest.
# ---------------------------------------------------------------------------

def _pretty(obj) -> bytes:
    """Pretty-print for the on-disk file (human-readable). The SHA is NOT over this form."""
    return json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=True).encode("utf-8") + b"\n"


def write_corpus(fixtures: list) -> dict:
    if FIXTURES_DIR.exists():
        for p in sorted(FIXTURES_DIR.glob("*.json")):
            p.unlink()
    FIXTURES_DIR.mkdir(parents=True, exist_ok=True)

    manifest_entries = []
    stage_counts = {}
    for fx in fixtures:
        fname = fx["id"].replace("/", "_") + ".json"
        (FIXTURES_DIR / fname).write_bytes(_pretty(fx))
        manifest_entries.append({
            "id": fx["id"],
            "stage": fx["stage"],
            "file": f"fixtures/{fname}",
            "input_sha256": fx["input_sha256"],
            "expected_sha256": fx["expected_sha256"],
            "fixture_sha256": fx["fixture_sha256"],
        })
        stage_counts[fx["stage"]] = stage_counts.get(fx["stage"], 0) + 1

    # Manifest-level SHA: SHA over the canonical-JSON of all `fixture_sha256` in order
    # (this IS the corpus version id - a single byte changes -> manifest sha changes).
    fixture_shas = [e["fixture_sha256"] for e in manifest_entries]
    corpus_sha = sha256(canon(fixture_shas))

    manifest = {
        "version": CORPUS_VERSION,
        "spec": (
            "lean/Chanlun/*.lean (Normalize, Fractal, Stroke, Zhongshu, TrendType, "
            "LevelRecursion, BiReachableDeterminism, Pipeline) + chanlun.md (definitions 2-5, "
            "lessons 17/20/24)."
        ),
        "reference_backend": "conformance/chanlun-v1/reference_backend/",
        "canonical_json": {
            "sort_keys": True,
            "separators": [",", ":"],
            "ensure_ascii": True,
            "note": (
                "fixture_sha256 = SHA-256( canonical(input) + '|' + canonical(expected) ). "
                "corpus_sha256 = SHA-256( canonical([fixture_sha256 for each entry in order]) )."
            ),
        },
        "stage_counts": stage_counts,
        "count": len(manifest_entries),
        "corpus_sha256": corpus_sha,
        "entries": manifest_entries,
    }
    MANIFEST_PATH.write_bytes(_pretty(manifest))
    return manifest


def main() -> int:
    fxs = collect_fixtures()
    manifest = write_corpus(fxs)
    print(f"chanlun-v1 corpus written: {manifest['count']} fixtures across {len(manifest['stage_counts'])} stages")
    for stage, cnt in sorted(manifest["stage_counts"].items()):
        print(f"  {stage:12s}  {cnt:4d}")
    print(f"corpus_sha256 = {manifest['corpus_sha256']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
