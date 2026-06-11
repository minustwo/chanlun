# Chanlun conformance corpus - `chanlun-v1`

> The portable, language-agnostic test suite for the Chanlun (chanlun) deterministic
> decomposition pipeline. A backend in ANY language that reproduces every fixture's
> SHA-256 expected output is conformant to `chanlun-v1`. No Python required to
> consume it.

This corpus FREEZES the Chanlun decomposition spec: `bars -> normalize -> fractal -> stroke
-> zhongshu -> trend_type`. Each fixture pins (input bytes -> expected output bytes) under
canonical-JSON SHA-256. A byte off = non-conformant. There is no fuzzy comparison.

## Files

| file | what |
|---|---|
| `manifest.json` | Spec pointer + per-fixture SHA-256 expectations + corpus_sha256 (the conformance-version id). |
| `fixtures/*.json` | One JSON file per fixture: `{ id, stage, input, expected, input_sha256, expected_sha256, fixture_sha256 }`. |
| `reference_backend/` | Pure-stdlib Python reference (`normalize`, `fractal`, `strokes`, `zhongshu`, `trend_type`, `pipeline`). |
| `runner.py` | Reference runner (<100 lines pure stdlib): re-runs the reference backend on each fixture and asserts byte-equality. |
| `generate_corpus.py` | Deterministic fixture generator (re-run produces identical bytes). |
| `example_phase3_check.py` | Template script for a Phase-3 implementor: load fixtures, run your pipeline, compare SHA-256. |

## How to run

```bash
# Verify every fixture matches the frozen spec (reference Python).
python3 conformance/chanlun-v1/runner.py
# 48 PASS, 0 FAIL => conformant to chanlun-v1.

# Verify with --verbose (shows per-fixture sha).
python3 conformance/chanlun-v1/runner.py --verbose

# Regenerate the corpus (deterministic - same bytes).
python3 conformance/chanlun-v1/generate_corpus.py
# Same corpus_sha256 = the frozen conformance-version id.
```

## What's in the corpus

48 fixtures across 6 stages of the Chanlun pipeline (`stage_counts` from `manifest.json`).

| stage | count | what it tests |
|---|---:|---|
| `normalize` | 10 | Algorithm N (`chanlun.md` Appendix A) - single-pass containment normalization. |
| `fractal` | 7 | Definition 3 fractal classification on a 3-bar window (top / bottom). |
| `stroke` | 6 | Definition 4 + Lemma 2 stroke greedy (alternation + separation `>= dmin`). |
| `zhongshu` | 9 | Center decomposition (3-overlap rule, `first3` and `all` zone gates). |
| `trend_type` | 8 | Walk type classifier (consolidation / trend_up / trend_down / mixed / none) per lesson 17. |
| `pipeline` | 8 | End-to-end (bars -> trend type) over deterministic seeded walks. |

Each category includes:

- **Hand fixtures** - small, named cases that exercise one specific invariant (e.g.
  `normalize.hand_single_containment`, `fractal.hand_top`, `zhongshu.hand_no_overlap`).
- **Synthetic fixtures** - seeded random-walk inputs of varying lengths to broaden coverage
  (e.g. `normalize.synth_walk_seed101_n10`, `pipeline.synth_walk_seed3004_n320`).

## The wire shape (what a Phase-3 backend reads / writes)

Each fixture is the canonical JSON:

```json
{
  "id":               "stroke.hand_one_down",
  "stage":            "stroke",
  "description":      "Top at idx 0, bottom at idx 5 with gap >= dmin=3 -> one down-stroke; ...",
  "input":            { "fractals": [...], "dmin": 3 },
  "expected":         { "strokes": [...], "dispositions": ["first","emit","residue"] },
  "input_sha256":     "<sha256 of canonical(input)>",
  "expected_sha256":  "<sha256 of canonical(expected)>",
  "fixture_sha256":   "<sha256 of canonical(input) + '|' + canonical(expected)>"
}
```

### Canonical JSON

For every SHA-256 computation, the bytes are produced via:

```python
json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
```

i.e. keys sorted, no whitespace, ASCII-escape non-ASCII. Every Phase-3 implementation
MUST reproduce these bytes byte-for-byte to be conformant.

### Stage input / output shapes

| stage | input shape | output shape |
|---|---|---|
| `normalize` | `[ {l:int, h:int}, ... ]` | `[ {l:int, h:int}, ... ]` (no adjacent containment) |
| `fractal` | `[ {l:int, h:int}, ... ]` (normalized bars) | `[ {idx:int, kind:"top"|"bottom", h:int, l:int}, ... ]` |
| `stroke` | `{ fractals: [...], dmin: int }` | `{ strokes: [...], dispositions: ["first"|"absorbed"|"emit"|"residue", ...] }` |
| `zhongshu` | `{ elements: [{idx, lo, hi}, ...], zone: "first3"|"all" }` | `[ {start:int, end:int, ZD:int, ZG:int, n:int}, ... ]` |
| `trend_type` | `[ {start, end, ZD, ZG, n}, ... ]` (centers) | `"consolidation"|"trend_up"|"trend_down"|"mixed"|"none"` |
| `pipeline` | `{ bars, dmin?, zone? }` | `{ normalized_bars, fractals, stroke_dispositions, strokes, stroke_elements, zhongshu_zone, zhongshu_centers, trend_type }` |

## How to write a conforming Phase-3 backend

1. **Read the spec**:
   - `chanlun.md` (English) / `chanlun.zh.md` (Chinese) - Definitions 2-5, lessons 17/20/24.
   - `lean/Chanlun/*.lean` - the machine-verified theorems (`fractal_slot_equiv_def3`,
     `normalize_no_adjacent_containment`, `stroke_emit_alternates_and_separates`, ...).
   - `grounding/chanlun_*_grounding.py` - the pure-Python oracles (themselves a downstream
     of the kernel-verified Lean library).
2. **Implement** each stage in your target language.
3. **Run the corpus**: for each `entries[i]` in `manifest.json`,
   - load `fixtures/<file>.json`;
   - run your pipeline on `input`;
   - canonicalize the output (`sort_keys=True, separators=",:"`, ASCII-escape);
   - SHA-256(canonical_output) MUST equal `expected_sha256`. A byte off = non-conformant.
4. **Pass all 48 fixtures** -> your backend is conformant to `chanlun-v1`.

Treat `example_phase3_check.py` as the template (the entire script is ~60 lines pure stdlib).

## Lineage (where the expected values come from)

```
                  lesson 17/20/24                   (chanlun.md / chanlun.zh.md - the formal system)
                         |
                         v
                  Lean MWEs                          (lean/Chanlun/*.lean - kernel-verified theorems)
                         |
                         v
                  Python groundings                  (grounding/chanlun_*_grounding.py - pure-stdlib oracles, sealed)
                         |
                         v
                  Reference backend                  (conformance/chanlun-v1/reference_backend/ - standalone modules)
                         |
                         v
                  Fixtures + manifest                (THIS CORPUS)
```

Every step is auditable. A Phase-3 implementation that conforms to this corpus is, by
transitivity, conforming to the verified Lean library.

## Versioning

This is `chanlun-v1`, FROZEN. The `manifest.json#corpus_sha256` is the version id:
**`df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`**.

A new corpus version (`chanlun-v2`, ...) would live in its OWN directory
(`conformance/chanlun-v2/`). v1 NEVER changes. A change to the reference backend that alters
ANY fixture's expected SHA is a backwards-incompatible change and goes into a new version.

## CI gate

The `chanlun-gate` workflow (`.github/workflows/chanlun-gate.yml`) runs `python3
conformance/chanlun-v1/runner.py` on every push to `main` and every PR. A non-zero exit code
fails the build. This is the hosted-Ubuntu enforcement that the FROZEN spec stays frozen.

## SS15 red line

> SHA-equality is the law. A byte off = FAIL. No "approximately equal", no float tolerance,
> no fuzzy match. If you relax a fixture to make it pass, you've broken the spec.

If a fixture's expected output looks WRONG to a Phase-3 implementor, do NOT relax it.
Open a `[chanlun_v1_fixture_F_questionable_OPEN]` named-residue ticket, surface it in
the runner output, and resolve in a follow-up `chanlun-v2` corpus version.

## Pure-stdlib runner

The runner uses ONLY Python's standard library (no numpy, no pandas, no external deps). This
makes it trivial to mirror in any Phase-3 language: the canonical-JSON + SHA-256 stack is
universal.
