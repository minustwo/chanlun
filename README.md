# Chanlun — Theory + Lean Formalization

A formalized geometric decomposition system for **Chanlun** (the theory
taught by Master Chanzhongshuochan) technical analysis, with:

* **Theory document**: [`chanlun.md`](chanlun.md) (mathematical formalism).
* **Lean 4 formalization** (`lean/Chanlun/`): the 21 load-bearing
  modules below, all `sorry`-free, kernel-verified on hosted Ubuntu CI.
* **Pure-Python groundings** (`grounding/`): independent reference
  oracles for each Lean theorem, with §15 falsifying mutants.

Chinese version: see [README.zh.md](README.zh.md).

> **Attribution.** The Chanlun theory itself belongs to the
> Chanzhongshuochan tradition. The mathematical formalism in
> [`chanlun.md`](chanlun.md) is this repository's narrative form of the
> Lean library; the Lean modules in `lean/Chanlun/` are the trusted
> artifact. The Lean formalization in
> `lean/Chanlun/` (this directory's contribution) was developed inside
> the [`codex-proof-workbench`](https://github.com/minustwo/codex-proof-workbench)
> proof program and migrated here for public availability.

---

## Status — what is proven, what is named-open

The Lean library `Chanlun` (`lake build Chanlun`) is sorry-free and
covers the four-stage published pipeline plus follow-up structural and
buy/sell-point layers (Zhongshu, WalkType, Beichi, BSPs, interval-nested
decomposition). Twenty-one modules:

### Core pipeline (Def-3 → Stroke → Segment → Zhongshu)

| Module | Theorems (chanlun.md reference) |
|---|---|
| `Chanlun.Fractal` | Def-3 (Fenxing): `fractal_slot_equiv_def3`, `def3_trichotomy` (Lemma 1), `def3_admissible_classifies`, `def3_residue_iff_neither` |
| `Chanlun.Normalize` | Algorithm N (containment handling, Appendix A): `normalize_no_adjacent_containment` (single-pass = full-collapse) |
| `Chanlun.Pipeline` | N → Def-3 composition: `pipeline_inclusion_normalized`, `pipeline_fractal_classification_well_defined` |
| `Chanlun.Stroke` | Def-4 (Bi, leftmost-greedy): `stroke_emits_separated` (B), `stroke_emits_alternate` (A), `strokes_separated` |
| `Chanlun.StrokeUniqueness` | Lemma 2 strong form: `strokes_unique` (any `IsValidBi` = canonical streaming output) |
| `Chanlun.StrokesIsValidBiCorollary` | Lemma 2 non-vacuity + biconditional: `strokes_isValidBi`, `strokes_iff_IsValidBi` |
| `Chanlun.BiEndpointSubResidues` | PR #1090 §3 sub-residues: `to_endpoint_leftmost_eq_extremal_on_reachable`, `dropBranch_preserves_IsValidBi`, `allAlternate_reverse`, `strokes_alternate` |
| `Chanlun.Segment` | Def 5–16 + Theorem 1 (Xianduan + parameterized unique segment decomposition): `segments_partition` (P), `segments_terminate` (T), `segment_advance_strictly_increasing` |
| `Chanlun.Zhongshu` | Zhongshu (lesson 17/20): `zhongshu_valid`, `zhongshu_disjoint`, `extendEnd_ge`, parameterized over `ZoneGate ∈ {first3, all_}` |
| `Chanlun.ZhongshuExtension` | 中枢 延伸 / 扩展 / 新生 / 9-段升级 (lesson 17/20/30): `classifyExtension_total`, `extension_preserves_core_ZD_ZG`, `expansion_widens_GG_DD`, `rebirth_creates_disjoint_core`, `upgrade_trigger_iff_9_segments` |
| `Chanlun.TrendType` | Consolidation / Trend (lesson 17): `classify_total`, `classify_trend_monotone` (sequentially-same-direction is genuinely monotone) |
| `Chanlun.WalkDecomposition` | Maximal walk decomposition (lesson 17): `decompose_partition`, `decompose_monotonic`, `decompose_type_homogeneous`, `decompose_unique` |

### Reachable-domain determinism

| Module | Theorems |
|---|---|
| `Chanlun.BiReachableDeterminism` | Reachable-domain determinism: `fractals_alternate_on_containment_free` (post-normalize ⇒ Fenxings strictly alternate ⇒ the three Bi-endpoint readings COINCIDE on reachable inputs) |
| `Chanlun.BiReachableDeterminismBridge` | Bar↔Interval bridge: `map_toBar_preserves_noAdjContainment`, `normalize_then_fractals_alternate` (raw `Interval` ⇒ alternation one-shot) |

### Buy/sell points + 背驰 (lessons 20/24/27/29/37)

| Module | Theorems |
|---|---|
| `Chanlun.Beichi` | 背驰 力度 comparison (lessons 24/27/29): `classifyBeichi_total`, `beichi_irrefl`, `beichi_load_bearing` (disp + slope cross-product), `beichi_measure_gate_witness` (§15 non-vacuity of `disp` vs `slope`) |
| `Chanlun.PanzhengBeichi` | 盘整背驰 (lesson 37): single-center A-vs-C classifier, `classify_panzheng_total`, `panzheng_load_bearing_disp`/`slope`, `panzheng_measure_gate_witness`, `panzheng_intra_vs_inter_load_bearing` |
| `Chanlun.ThirdBuysell` | 第三类买卖点 (lesson 20): `classifyBsp_total`, `bsp_zone_load_bearing`, `bsp_reenter_up_iff` / `bsp_reenter_down_iff`, `bsp_excl` |
| `Chanlun.FirstSecondBuysell` | 第一/第二类买卖点 (lesson 24): `classify_total`, `classify_first_point_only_total`, `second_not_breaking_iff`, `first_point_failed_iff`, `first_second_inheritance_load_bearing` (named gate inheritance) |
| `Chanlun.RecursiveSubBspBeichi` | Recursive 三买卖 + 背驰 (lessons 20/24/27/29 推广至 次级别): `recursive_subBsp_fuel_stationary`, `recursive_subBsp_terminates`, `recursive_subBsp_inheritance`, `recursive_subBsp_total`, `recursive_subBsp_fuel_bound_via_levelRecursion` |

### 级别 recursion + 区间套

| Module | Theorems |
|---|---|
| `Chanlun.LevelRecursion` | "Every trend must complete" (lesson 24): `centerSize_ge_3`, `lift_strict_drop` (≥2 element drop per non-terminal lift ⇒ level recursion terminates in ≤ n/2 levels) |
| `Chanlun.IntervalNesting` | 区间套 (lessons 65–66): `intervalnesting_terminates`, `walk_always_has_verdict`, `intervalnesting_pin_monotone`, `intervalnesting_chain_strict_drop`, `walk_at_zero_returns_gate_limit`, `walk_at_positive_returns_pinned` |

### Honest scope — named-open follow-ups (not proven yet)

These are deliberately surfaced as named residues per Klaus's
`[..._OPEN]` discipline:

* `[chanlun_inclusion_precondition]` — the precondition Def-3 assumes
  upstream of `isInclusionNormalized`; discharged by the pipeline composition
  (`Chanlun.Pipeline.pipeline_inclusion_normalized`) but the type bridge is
  named explicitly.
* `[chanlun_segment_terminates_sub_OPEN]` — the feature-sequence Φ +
  overlap admissibility internals of `find_term` are NOT re-derived in
  `Chanlun.Segment`; the recursion is parameterized over the
  leftmost-≥-a contract `find_term_ge`.
* `[chanlun_zhongshu_zone_gate_OPEN]` — `first3` vs `all_` differ on ~12%
  of element sequences; both are proven `valid` + `disjoint`, but the
  gate-relativity is named.
* `[chanlun_bi_to_endpoint_first_admissible_OPEN]` —
  `Chanlun.StrokeUniqueness` reads the TO-endpoint as the LEFTMOST
  opposite-kind admissible Fenxing; a literal-strong reading of
  "extremal of the to-side run" could differ on multi-Fenxing runs.
* `[chanlun_bi_close_drop_named_residue_OPEN]` — opposite-close Fenxings
  (gap < δmin) are silently dropped by `step`; the uniqueness
  proof treats drops as no-ops.
* `[chanlun_stroke_output_order_lift_OPEN]` — `strokes_separated`
  lifts to the user-facing reversed order via `List.mem_reverse`;
  alternation-on-reverse is a separate one-liner left open.
* `[chanlun_level_recursion_lift_function_OPEN]` — the actual
  `lift : List Element → Option (List Element)` function is out of
  scope; only the strict-drop measure (the load-bearing termination
  half) is proven.
* `[chanlun_level_recursion_envelope_soundness_OPEN]` — each
  level-`(n+1)` envelope contains its members' ranges.
* `[chanlun_level_recursion_determinism_preservation_OPEN]` —
  determinism preserved up the tower.
* `[chanlun_walk_decomposition_spec_unique_OPEN]` — the SPEC form of
  walk-decomposition uniqueness (any spec-satisfying function =
  `decompose`).
* `[chanlun_zhongshu_extension_shoulder_OPEN]` — the "kiss" case
  (`next_el.lo = ZG` or `next_el.hi = ZD`) is admitted as EXTENSION
  under the published `≤`-overlap reading; a strict `<` reading would
  name it rebirth-boundary.
* `[chanlun_zhongshu_extension_all_gate_OPEN]` — the `all_` zone-gate
  propagation of expansion (the `first3` form is closed in
  `Chanlun.ZhongshuExtension`).
* `[chanlun_zhongshu_extension_multistep_envelope_OPEN]` — multi-element
  envelope across a full 中枢; per-step proven, list-induction left open.
* `[chanlun_beichi_measure_gate_OPEN]` — the `disp` vs `slope` 力度
  measure gate is REAL (host grounding 82.2% agreement). The
  `beichi_measure_gate_witness` theorem certifies non-vacuity; the choice
  itself is NAMED.
* `[chanlun_beichi_macd_gate_OPEN]` — MACD as a measure-gate instance
  (lesson 27's 辅助 tool, explicitly named non-canonical).
* `[chanlun_panzheng_measure_gate_propagation_OPEN]` — propagation of
  the 盘整背驰 measure gate across the §15 mutant table.
* `[chanlun_first_second_buysell_recursive_OPEN]` — recursive form of
  lessons-24 第一/第二类买卖点 (sits on the same descent + the
  measure-gate inheritance).
* `[chanlun_panzheng_beichi_recursive_OPEN]` — recursive form of
  盘整背驰 (lesson 37).
* `[chanlun_recursive_descent_strict_subwindow_OPEN]` — the strict
  proof that the level-(n-1) sub-window is a STRICT subset of the
  level-(n-1) tower.
* `[chanlun_intervalnesting_lowest_level_OPEN]` — the strict
  characterisation of the lowest-level pin endpoint.
* `[chanlun_intervalnesting_multiscale_OPEN]` — multi-scale composition
  of nested intervals across non-adjacent levels.
* `[chanlun_intervalnesting_macd_OPEN]` — MACD-decorated 区间套
  variant.
* `[chanlun_walk_decomposition_intervalnesting_OPEN]` — interval-nesting
  multi-level nested decomposition (joined to `Chanlun.IntervalNesting`).

These are NOT silent gaps — each is named so the next pass knows exactly
what residue to discharge.

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

A green `lake build Chanlun` verifies all 21 modules sorry-free under
the Lean kernel.

### Run the groundings

```bash
cd grounding
for f in chanlun_*_grounding.py; do
  echo "===== $f ====="
  PYTHONPATH=. python3 "$f"
done
```

Each grounding runs in a few seconds (60k–240k random sequences each)
and prints a one-line OK summary plus the §15 falsifiability check. No
external Python deps; pure stdlib + `random`.

---

## Layout

```
chanlun/
├─ chanlun.md                         # mathematical formalism (English)
├─ chanlun.zh.md                      # mathematical formalism (Chinese)
├─ README.md                          # this file (English)
├─ README.zh.md                       # Chinese version
├─ lakefile.lean, lean-toolchain      # Lean 4 build config (Mathlib v4.14.0)
├─ lean/Chanlun/                      # the 21 Lean MWE modules
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
├─ conformance/chanlun-v1/             # FROZEN conformance corpus (Phase-3 spec)
│  ├─ manifest.json                    # corpus_sha256 = the version id
│  ├─ fixtures/*.json                  # 48 (input, expected, sha) fixtures
│  ├─ reference_backend/               # standalone pure-stdlib reference (Python)
│  ├─ runner.py                        # ~100-line pure-stdlib verifier
│  ├─ generate_corpus.py               # deterministic fixture generator
│  ├─ example_phase3_check.py          # template for Phase-3 implementors
│  ├─ README.md, README.zh.md          # full spec docs (EN / ZH)
├─ impl/ts/                            # TypeScript port (Phase-3 multi-lang #1)
│  ├─ src/*.ts                         # six pipeline stages, no runtime deps
│  ├─ check.ts                         # 48-fixture conformance harness
│  ├─ package.json                     # devDeps only (typescript + @types/node)
│  └─ README.md, README.zh.md          # impl/ts docs (EN / ZH)
├─ impl/go/                            # Go (pure-stdlib) Phase-3 backend, passes all 48 fixtures
│  ├─ go.mod                           # github.com/minustwo/chanlun/impl/go, Go 1.22
│  ├─ cmd/check/main.go                # `go run ./cmd/check` runs the conformance harness
│  ├─ internal/chanlun/                # one file per stage, faithful port of the Python reference
│  └─ README.md, README.zh.md          # how to run, canonical-JSON choice, lineage
├─ impl/pinescript/                    # PineScript v5 backend (documented port)
│  ├─ chanlun_indicator.pine           # the indicator (load into TradingView)
│  ├─ PINESCRIPT_PORT.md               # per-stage mapping + 13 NAMED-OPEN residues
│  └─ README.md, README.zh.md          # EN/ZH usage docs (documentation-port-only — see below)
└─ .github/workflows/chanlun-gate.yml  # hosted Ubuntu CI: lake build + groundings + conformance (Python + TS + Go) + pinescript-lint
```

### PineScript backend — documentation-port-only

`impl/pinescript/` is a PineScript v5 port of the same algorithm. It plots
分型/笔/中枢 on real TradingView K-lines. **It is NOT conformance-verified**: PineScript
v5 cannot read the fixture corpus or compare SHA-256 in CI. The honesty discipline
surfaces every gap as a NAMED `[chanlun_v1_pinescript_<stage>_OPEN]` residue (13 in
total — see `impl/pinescript/PINESCRIPT_PORT.md`). The CI runs a DISCIPLINE check
(`conformance-pinescript-lint`) that verifies absence of anti-patterns and presence of
named residues — but it is NOT a SHA-equality gate.

---

## CI

The hosted-Ubuntu workflow `.github/workflows/chanlun-gate.yml` runs on
every push to `main` and every PR:

* `lean` job: installs `elan` + the pinned toolchain, restores
  `actions/cache@v4` over `.lake`, runs `lake exe cache get` to pull
  Mathlib's pre-built oleans, then `lake build Chanlun`. Final gate
  rejects any `sorry` keyword in `lean/Chanlun/*.lean`.
* `grounding` job: runs each `grounding/chanlun_*_grounding.py` with
  pure-stdlib Python 3.11.
* `conformance` job: runs `python3 conformance/chanlun-v1/runner.py` to
  verify every fixture matches the FROZEN spec byte-for-byte, then
  regenerates the corpus and confirms the bytes are identical (catches
  any reference-backend drift). The corpus_sha256 of `chanlun-v1` IS
  the conformance-version id: a Phase-3 multi-language implementation
  in any language is conformant iff it reproduces every fixture's
  expected SHA-256.
* `conformance-ts` job: installs Node 20, compiles `impl/ts/` (devDeps
  only: `typescript` + `@types/node`), and runs `impl/ts/dist/check.js`
  to verify the TypeScript backend reproduces every fixture's
  `expected_sha256` byte-for-byte. The job exits non-zero on any
  divergence - SHA-equality is the law, no fuzzy match.
* `conformance-go` job: builds the Go Phase-3 backend at `impl/go/` and
  runs `go run ./cmd/check`, which loads the same `manifest.json` and
  proves each fixture's SHA-256 reproduces under the Go port too. Go
  1.22, pure stdlib, no third-party dependencies. SHA-equality remains
  the law — non-zero exit fails the gate, never silently skips.

The Lean job typically takes ~5 minutes on a warm cache, ~25 minutes
cold. Groundings finish in ~30 seconds total. Conformance finishes in
under a minute.

---

## Cross-references

* The proof program these MWE files were developed in:
  [`codex-proof-workbench`](https://github.com/minustwo/codex-proof-workbench)
* Master Chan's published lessons (108-lesson series) are the
  source-of-truth for Zhongshu, WalkType, and the buy-sell-point
  geometry hooks used in the follow-up work.
* Mathlib v4.14.0 is the only library dependency.

---

## License

The mathematical formalism documents (`chanlun.md`, `chanlun.zh.md`),
the Lean formalization, groundings, and CI workflow are MIT-licensed
(see [`LICENSE`](LICENSE) if present in the repo).
