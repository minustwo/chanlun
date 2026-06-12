# Chanlun — Theory + Lean Formalization

A kernel-verified Lean 4 formalization of **Chanlun** (缠论), the geometric
technical-analysis theory taught by master 缠中说禅, paired with an executable
pure-Python reference backend and multi-language ports.

* **Theory document**: [`chanlun.md`](chanlun.md) — the mathematical formalism.
* **Lean 4 formalization** (`lean/Chanlun/`): 21 modules covering the published
  pipeline plus structural/buy-sell layers. All modules are kernel-verified on
  hosted Ubuntu CI with no admitted lemmas (`sorry`-free).
* **Pure-Python reference oracles** (`grounding/`): independent implementations
  of each Lean theorem with falsifying mutation tests.
* **Frozen conformance corpus** (`conformance/chanlun-v1/`): a byte-exact,
  language-agnostic test suite. 48 fixtures × 6 stages, SHA-256 locked.
* **Multi-language ports** (`impl/`): TypeScript, Go, and PineScript backends
  exercising the same algorithm.

Chinese version: see [README.zh.md](README.zh.md).

> **Attribution.** The Chanlun theory itself belongs to the 缠中说禅 tradition.
> The mathematical formalism in [`chanlun.md`](chanlun.md) is this repository's
> narrative form of the Lean library; the Lean modules in `lean/Chanlun/` are
> the trusted artifact.

---

## TL;DR

Chanlun is a deterministic decomposition of a price series into geometric
units (fractals 分型 → strokes 笔 → segments 线段 → centers 中枢 → walks 走势).
This repository (a) formalizes the decomposition in Lean 4 so its main
correctness properties are machine-checked, (b) provides an executable
reference backend whose outputs are byte-frozen as a conformance corpus, and
(c) ports the reference to TypeScript, Go, and PineScript.

* **Proven**: 21 Lean modules covering Definitions 3 and 4, Algorithm N
  (containment normalization), Lemma 2 (stroke uniqueness), Theorem 1
  (segment decomposition termination), the central-zone (中枢) construction,
  the walk-type classifier, and recursive buy/sell-point layers.
* **Open**: a list of explicitly named limitations is given in
  *Known limitations and open questions* below. Each one is surfaced rather
  than hidden.
* **Start here**: the theory write-up in [`chanlun.md`](chanlun.md), then the
  Lean modules in [`lean/Chanlun/`](lean/Chanlun/), then the conformance corpus
  in [`conformance/chanlun-v1/`](conformance/chanlun-v1/).

---

## Proven results

The Lean library `Chanlun` (built via `lake build Chanlun`) is `sorry`-free
and covers the four-stage published pipeline plus structural/buy-sell layers.
21 modules:

### Core pipeline (Def-3 → Stroke → Segment → Zhongshu)

| Module | Theorems (chanlun.md reference) |
|---|---|
| `Chanlun.Fractal` | Def-3 (Fenxing): `fractal_slot_equiv_def3`, `def3_trichotomy` (Lemma 1), `def3_admissible_classifies`, `def3_residue_iff_neither` |
| `Chanlun.Normalize` | Algorithm N (containment handling, Appendix A): `normalize_no_adjacent_containment` (single-pass = full-collapse) |
| `Chanlun.Pipeline` | N → Def-3 composition: `pipeline_inclusion_normalized`, `pipeline_fractal_classification_well_defined` |
| `Chanlun.Stroke` | Def-4 (Bi, leftmost-greedy): `stroke_emits_separated` (B), `stroke_emits_alternate` (A), `strokes_separated` |
| `Chanlun.StrokeUniqueness` | Lemma 2 strong form: `strokes_unique` (any `IsValidBi` = canonical streaming output) |
| `Chanlun.StrokesIsValidBiCorollary` | Lemma 2 non-vacuity + biconditional: `strokes_isValidBi`, `strokes_iff_IsValidBi` |
| `Chanlun.BiEndpointSubResidues` | Sub-results on Bi endpoints: `to_endpoint_leftmost_eq_extremal_on_reachable`, `dropBranch_preserves_IsValidBi`, `allAlternate_reverse`, `strokes_alternate` |
| `Chanlun.Segment` | Def 5–16 + Theorem 1 (Xianduan + parameterized unique segment decomposition): `segments_partition` (P), `segments_terminate` (T), `segment_advance_strictly_increasing` |
| `Chanlun.Zhongshu` | Zhongshu 中枢 (lesson 17/20): `zhongshu_valid`, `zhongshu_disjoint`, `extendEnd_ge`, parameterized over `ZoneGate ∈ {first3, all_}` |
| `Chanlun.ZhongshuExtension` | 中枢 延伸 / 扩展 / 新生 / 9-段升级 (lesson 17/20/30): `classifyExtension_total`, `extension_preserves_core_ZD_ZG`, `expansion_widens_GG_DD`, `rebirth_creates_disjoint_core`, `upgrade_trigger_iff_9_segments` |
| `Chanlun.TrendType` | Consolidation 盘整 / Trend 趋势 (lesson 17): `classify_total`, `classify_trend_monotone` |
| `Chanlun.WalkDecomposition` | Maximal walk decomposition (lesson 17): `decompose_partition`, `decompose_monotonic`, `decompose_type_homogeneous`, `decompose_unique` |

### Reachable-domain determinism

| Module | Theorems |
|---|---|
| `Chanlun.BiReachableDeterminism` | Reachable-domain determinism: `fractals_alternate_on_containment_free` (post-normalize ⇒ fractals strictly alternate ⇒ the three Bi-endpoint readings coincide on reachable inputs) |
| `Chanlun.BiReachableDeterminismBridge` | Bar↔Interval bridge: `map_toBar_preserves_noAdjContainment`, `normalize_then_fractals_alternate` (raw `Interval` ⇒ alternation one-shot) |

### Buy/sell points + divergence 背驰 (lessons 20/24/27/29/37)

| Module | Theorems |
|---|---|
| `Chanlun.Beichi` | 背驰 strength comparison (lessons 24/27/29): `classifyBeichi_total`, `beichi_irrefl`, `beichi_load_bearing` (displacement + slope cross-product), `beichi_measure_gate_witness` |
| `Chanlun.PanzhengBeichi` | 盘整背驰 (lesson 37): single-center A-vs-C classifier, `classify_panzheng_total`, `panzheng_load_bearing_disp`/`slope`, `panzheng_measure_gate_witness`, `panzheng_intra_vs_inter_load_bearing` |
| `Chanlun.ThirdBuysell` | 第三类买卖点 (lesson 20): `classifyBsp_total`, `bsp_zone_load_bearing`, `bsp_reenter_up_iff` / `bsp_reenter_down_iff`, `bsp_excl` |
| `Chanlun.FirstSecondBuysell` | 第一/第二类买卖点 (lesson 24): `classify_total`, `classify_first_point_only_total`, `second_not_breaking_iff`, `first_point_failed_iff`, `first_second_inheritance_load_bearing` |
| `Chanlun.RecursiveSubBspBeichi` | Recursive buy/sell + divergence (lessons 20/24/27/29 lifted to sub-levels): `recursive_subBsp_fuel_stationary`, `recursive_subBsp_terminates`, `recursive_subBsp_inheritance`, `recursive_subBsp_total`, `recursive_subBsp_fuel_bound_via_levelRecursion` |

### Level recursion + nested intervals 区间套

| Module | Theorems |
|---|---|
| `Chanlun.LevelRecursion` | "Every trend must complete" (lesson 24): `centerSize_ge_3`, `lift_strict_drop` (≥2 element drop per non-terminal lift ⇒ level recursion terminates in ≤ n/2 levels) |
| `Chanlun.IntervalNesting` | 区间套 (lessons 65–66): `intervalnesting_terminates`, `walk_always_has_verdict`, `intervalnesting_pin_monotone`, `intervalnesting_chain_strict_drop`, `walk_at_zero_returns_gate_limit`, `walk_at_positive_returns_pinned` |

---

## Known limitations and open questions

The following items are not (yet) proven inside the Lean library. They are
listed here so the scope is explicit rather than hidden.

* **Containment precondition bridge.** `Chanlun.Pipeline.pipeline_inclusion_normalized`
  discharges the precondition Def-3 assumes upstream, but the type bridge
  between the `Interval`-level and `Bar`-level statements is named explicitly
  and not folded into a single theorem.
* **Segment recursion internals.** The feature-sequence Φ + overlap
  admissibility internals of `find_term` are not re-derived in
  `Chanlun.Segment`; the recursion is parameterized over the leftmost-≥-a
  contract `find_term_ge`. A concrete `find_term` instance satisfying the
  contract is taken as given.
* **Zhongshu zone-gate non-uniqueness.** The two zone-gate choices `first3`
  and `all_` disagree on roughly 12% of arbitrary element sequences. Both are
  proven `valid` and `disjoint`; the gate-relativity is a real artifact of
  how Chanlun's master text leaves the choice underspecified. On the
  reachable (containment-free) domain the two readings agree.
* **Bi to-endpoint reading.** `Chanlun.StrokeUniqueness` reads the
  TO-endpoint as the leftmost opposite-kind admissible fractal; a literal
  reading of "extremal of the to-side run" could differ on multi-fractal
  runs. Both readings coincide on reachable inputs (see
  `Chanlun.BiReachableDeterminism`).
* **Close-fractal drop.** Opposite-close fractals with gap `< δmin` are
  silently dropped by `step`; the uniqueness proof treats these drops as
  no-ops.
* **Reversed-order alternation lift.** `strokes_separated` lifts to the
  user-facing reversed order via `List.mem_reverse`; the
  alternation-on-reverse lift is a separate one-line lemma not yet included.
* **Level-recursion `lift` function.** The actual
  `lift : List Element → Option (List Element)` function is out of scope; we
  prove only the strict-drop measure (the part that carries the
  termination argument).
* **Level-recursion envelope soundness.** Each level-`(n+1)` envelope
  contains its members' ranges; not yet proven.
* **Level-recursion determinism preservation.** Determinism preserved up the
  level tower; not yet proven.
* **Walk-decomposition spec uniqueness.** Any function satisfying the
  walk-decomposition specification equals `decompose`. Not yet proven in
  spec form.
* **Zhongshu extension boundary cases.** The "kiss" case
  (`next_el.lo = ZG` or `next_el.hi = ZD`) is treated as extension under
  the published `≤`-overlap reading; a strict `<` reading would assign it
  to rebirth-boundary. Both readings appear in the master text; we follow
  the `≤` reading.
* **Zhongshu extension on `all_` gate.** The `first3` form of the expansion
  propagation is closed in `Chanlun.ZhongshuExtension`; the `all_` form is
  not.
* **Multi-step center envelope.** Multi-element envelope across a full
  center; per-step is proven, list-induction not yet.
* **Divergence strength measure.** Displacement (`disp`) and slope agree on
  ~82.2% of inputs in the Python oracles. The
  `beichi_measure_gate_witness` theorem certifies non-vacuity; choice of
  measure itself is left open (an artifact of how the master text describes
  strength comparison without fixing a single measure).
* **MACD as divergence measure.** Lesson 27 introduces MACD as an auxiliary
  strength measure; explicitly treated as non-canonical.
* **Divergence measure propagation in consolidation.** Propagation of the
  consolidation-divergence measure across the mutation table.
* **Recursive forms of 1st/2nd buy/sell and consolidation divergence.**
  The recursive (multi-level) forms of lessons 24 and 37 sit on the same
  descent measure plus measure-gate inheritance; not yet proven.
* **Strict sub-window for level recursion.** Strict proof that the
  level-`(n-1)` sub-window is a strict subset of the level-`(n-1)` tower.
* **Lowest-level pin and multiscale nesting.** Strict characterization of
  the lowest-level pin endpoint, and multi-scale composition of nested
  intervals across non-adjacent levels.
* **MACD-decorated nested intervals.** A variant of 区间套 instrumented
  with MACD.
* **Walk decomposition × nested intervals.** Joining
  `Chanlun.WalkDecomposition` to `Chanlun.IntervalNesting`.

---

## Build

### Prerequisites

* [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager)
* The pinned Lean version (`leanprover/lean4:v4.14.0`, set in `lean-toolchain`)

### Build the Lean library

```bash
# Resolve & download dependencies (Mathlib v4.14.0 + transitive).
lake update
# Download pre-built Mathlib oleans (works on free hosted runners).
lake exe cache get
# Build the Chanlun library.
lake build Chanlun
```

A successful `lake build Chanlun` certifies all 21 modules under the Lean
kernel with no admitted lemmas.

### Run the reference oracles

```bash
cd grounding
for f in chanlun_*_grounding.py; do
  echo "===== $f ====="
  PYTHONPATH=. python3 "$f"
done
```

Each oracle runs in a few seconds (60k–240k random sequences) and prints a
one-line OK summary plus a falsifying-mutant check. No external Python
dependencies; pure standard library plus `random`.

---

## Layout

```
chanlun/
├─ chanlun.md                         # mathematical formalism (English)
├─ chanlun.zh.md                      # mathematical formalism (Chinese)
├─ README.md                          # this file (English)
├─ README.zh.md                       # Chinese version
├─ lakefile.lean, lean-toolchain      # Lean 4 build config (Mathlib v4.14.0)
├─ lean/Chanlun/                      # the 21 Lean modules
│  ├─ Fractal.lean, Normalize.lean, Pipeline.lean
│  ├─ Stroke.lean, StrokeUniqueness.lean, StrokesIsValidBiCorollary.lean
│  ├─ BiEndpointSubResidues.lean
│  ├─ Segment.lean
│  ├─ Zhongshu.lean, ZhongshuExtension.lean
│  ├─ TrendType.lean, WalkDecomposition.lean
│  ├─ BiReachableDeterminism.lean, BiReachableDeterminismBridge.lean
│  ├─ Beichi.lean, PanzhengBeichi.lean
│  ├─ ThirdBuysell.lean, FirstSecondBuysell.lean
│  ├─ LevelRecursion.lean, RecursiveSubBspBeichi.lean
│  ├─ IntervalNesting.lean
├─ grounding/                         # pure-Python reference oracles
│  ├─ chanlun_inclusion_grounding.py
│  ├─ chanlun_singlepass_idempotent_grounding.py
│  ├─ chanlun_stroke_grounding.py
│  ├─ chanlun_trend_type_grounding.py
│  ├─ chanlun_zhongshu_grounding.py
│  ├─ chanlun_bi_endpoint_multivalued_grounding.py
│  └─ chanlun_bi_kline_rule_grounding.py
├─ conformance/chanlun-v1/             # frozen conformance corpus
│  ├─ manifest.json                    # corpus_sha256 = the version id
│  ├─ fixtures/*.json                  # 48 (input, expected, sha) fixtures
│  ├─ reference_backend/               # standalone pure-stdlib reference (Python)
│  ├─ runner.py                        # ~100-line pure-stdlib verifier
│  ├─ generate_corpus.py               # deterministic fixture generator
│  ├─ example_phase3_check.py          # template for downstream implementations
│  ├─ README.md, README.zh.md          # full spec docs (EN / ZH)
├─ impl/ts/                            # TypeScript port
│  ├─ src/*.ts                         # six pipeline stages, no runtime deps
│  ├─ check.ts                         # 48-fixture conformance harness
│  ├─ package.json                     # devDeps only (typescript + @types/node)
│  └─ README.md, README.zh.md
├─ impl/go/                            # Go (pure-stdlib) backend, passes all 48 fixtures
│  ├─ go.mod                           # github.com/minustwo/chanlun/impl/go, Go 1.22
│  ├─ cmd/check/main.go                # `go run ./cmd/check` runs the conformance harness
│  ├─ internal/chanlun/                # one file per stage, faithful port of the Python reference
│  └─ README.md, README.zh.md
├─ impl/pinescript/                    # PineScript v5 documentation port
│  ├─ chanlun_indicator.pine           # the indicator (load into TradingView)
│  ├─ PINESCRIPT_PORT.md               # per-stage mapping + named limitations
│  └─ README.md, README.zh.md
└─ .github/workflows/chanlun-gate.yml  # hosted Ubuntu CI: lake build + oracles + conformance + lint
```

### PineScript backend — documentation-only port

`impl/pinescript/` is a PineScript v5 port of the same algorithm. It plots
分型 / 笔 / 中枢 on real TradingView K-lines. **It is not conformance-verified.**
PineScript v5 cannot read the fixture corpus or compare SHA-256 in CI, so
each verification gap is surfaced explicitly in
`impl/pinescript/PINESCRIPT_PORT.md`. The CI runs a discipline check
(`conformance-pinescript-lint`) that looks for known anti-patterns and
verifies the limitations are documented — it is *not* a SHA-equality gate.

---

## CI

The hosted-Ubuntu workflow `.github/workflows/chanlun-gate.yml` runs on every
push to `main` and every PR:

* `lean` job: installs `elan` + the pinned toolchain, restores
  `actions/cache@v4` over `.lake`, runs `lake exe cache get` to pull
  Mathlib's pre-built oleans, then `lake build Chanlun`. A final gate
  rejects any `sorry` keyword in `lean/Chanlun/*.lean`.
* `grounding` job: runs each `grounding/chanlun_*_grounding.py` with
  pure-stdlib Python 3.11.
* `conformance` job: runs `python3 conformance/chanlun-v1/runner.py` to
  verify every fixture matches the frozen spec byte-for-byte, then
  regenerates the corpus and confirms the bytes are identical (catches
  any reference-backend drift). The `corpus_sha256` of `chanlun-v1` is
  the conformance version identifier: an implementation in any language
  is conformant iff it reproduces every fixture's `expected_sha256`.
* `conformance-ts` job: installs Node 20, compiles `impl/ts/` (devDeps
  only: `typescript` + `@types/node`), and runs `impl/ts/dist/check.js`
  to verify the TypeScript backend reproduces every fixture's
  `expected_sha256` byte-for-byte. The job exits non-zero on any
  divergence — SHA-equality is required, no fuzzy match.
* `conformance-go` job: builds the Go backend at `impl/go/` and runs
  `go run ./cmd/check`, which loads the same `manifest.json` and
  verifies each fixture's SHA-256 reproduces under the Go port. Go 1.22,
  pure stdlib, no third-party dependencies.

The Lean job typically takes ~5 minutes on a warm cache, ~25 minutes cold.
Oracles finish in ~30 seconds total. Conformance finishes in under a
minute.

---

## License

The mathematical formalism documents (`chanlun.md`, `chanlun.zh.md`), the
Lean formalization, oracles, and CI workflow are MIT-licensed (see
[`LICENSE`](LICENSE) if present in the repo). The Chanlun theory itself
belongs to the 缠中说禅 tradition.
