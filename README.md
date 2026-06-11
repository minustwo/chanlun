# Chanlun (缠论) — Theory + Lean Formalization

A formalized geometric decomposition system for **Chanlun** (缠论, "the
theory taught by Master 缠中说禅") technical analysis, with:

* **Theory documents** (Klaus, April 2026): `chanlun.pdf` (English),
  `chanlun_zh.pdf` (中文).
* **Lean 4 formalization** (`lean/Chanlun/`): the 11 load-bearing
  theorems below, all `sorry`-free, kernel-verified on hosted Ubuntu CI.
* **Pure-Python groundings** (`grounding/`): independent reference
  oracles for each Lean theorem, with §15 falsifying mutants.

> **Attribution.** The 缠论 theory itself belongs to 缠中说禅 (the
> chanzhongshuochan tradition). The formal system in `chanlun{,_zh}.pdf`
> is Klaus's published formalization. The Lean formalization in
> `lean/Chanlun/` (this directory's contribution) was developed inside
> the [`codex-proof-workbench`](https://github.com/minustwo/codex-proof-workbench)
> proof program and migrated here for public availability.

---

## Status — what is proven, what is named-open

The Lean library `Chanlun` (`lake build Chanlun`) is sorry-free and
covers the four-stage published pipeline plus two follow-up structural
layers (中枢 / 走势类型). Eleven modules:

| Module | Theorems (chanlun.pdf reference) |
|---|---|
| `Chanlun.Fractal` | Def-3 (分型): `fractal_slot_equiv_def3`, `def3_trichotomy` (Lemma 1), `def3_admissible_classifies`, `def3_residue_iff_neither` |
| `Chanlun.Normalize` | Algorithm N (包含处理, Appendix A): `normalize_no_adjacent_containment` (single-pass ≡ full-collapse) |
| `Chanlun.Pipeline` | N → Def-3 composition: `pipeline_inclusion_normalized`, `pipeline_fractal_classification_well_defined` |
| `Chanlun.Stroke` | Def-4 (笔, leftmost-greedy): `stroke_emits_separated` (B), `stroke_emits_alternate` (A), `strokes_separated` |
| `Chanlun.StrokeUniqueness` | Lemma 2 strong form: `strokes_unique` (any `IsValidBi` ≡ canonical streaming output) |
| `Chanlun.Segment` | Def 5–16 + Theorem 1 (线段 + parameterized unique segment decomposition): `segments_partition` (P), `segments_terminate` (T), `segment_advance_strictly_increasing` |
| `Chanlun.Zhongshu` | 中枢 (走势中枢, 108课 lesson 17/20): `zhongshu_valid`, `zhongshu_disjoint`, `extendEnd_ge`, parameterized over `ZoneGate ∈ {first3, all_}` |
| `Chanlun.TrendType` | 盘整 / 趋势 (108课 lesson 17): `classify_total`, `classify_trend_monotone` (依次同向 is genuinely monotone) |
| `Chanlun.BiReachableDeterminism` | Reachable-domain determinism: `fractals_alternate_on_containment_free` (post-normalize ⇒ 分型 strictly alternates ⇒ the three 笔-endpoint readings COINCIDE on reachable inputs) |
| `Chanlun.LevelRecursion` | 走势必完美 (lesson 24): `centerSize_ge_3`, `lift_strict_drop` (≥2 element drop per non-terminal lift ⇒ level recursion terminates in ≤ `n/2` levels) |
| `Chanlun.WalkDecomposition` | 走势 maximal decomposition (lesson 17): `decompose_partition`, `decompose_monotonic`, `decompose_type_homogeneous` |

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
* `[chanlun_bi_to_endpoint_first_admissible_OPEN]` — `Chanlun.StrokeUniqueness`
  reads the TO-endpoint as the LEFTMOST opposite-kind admissible
  fractal; a literal-strong reading of "extremal of the to-side run"
  could differ on multi-fractal runs.
* `[chanlun_bi_close_drop_named_residue_OPEN]` — opposite-close
  fractals (gap < δmin) are silently dropped by `step`; the uniqueness
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
  walk-decomposition uniqueness (any spec-satisfying function ≡ `decompose`).
* `[chanlun_walk_decomposition_intervalnesting_OPEN]` — 区间套 / multi-level
  nested decomposition.

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
# Download pre-built Mathlib oleans (THE WIN — works on free hosted runners).
lake exe cache get
# Build the Chanlun library.
lake build Chanlun
```

A green `lake build Chanlun` verifies all 11 modules sorry-free under
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
├─ chanlun.pdf, chanlun_zh.pdf       # the theory (Klaus, April 2026)
├─ README.md                          # this file
├─ lakefile.lean, lean-toolchain      # Lean 4 build config (Mathlib v4.14.0)
├─ lean/Chanlun/                      # the 11 Lean MWE modules
│  ├─ Fractal.lean, Normalize.lean, Pipeline.lean
│  ├─ Stroke.lean, StrokeUniqueness.lean, Segment.lean
│  ├─ Zhongshu.lean, TrendType.lean, BiReachableDeterminism.lean
│  ├─ LevelRecursion.lean, WalkDecomposition.lean
├─ grounding/                         # pure-Python reference oracles
│  ├─ chanlun_inclusion_grounding.py
│  ├─ chanlun_singlepass_idempotent_grounding.py
│  ├─ chanlun_stroke_grounding.py
│  ├─ chanlun_trend_type_grounding.py
│  ├─ chanlun_zhongshu_grounding.py
│  ├─ chanlun_bi_endpoint_multivalued_grounding.py
│  └─ chanlun_bi_kline_rule_grounding.py
└─ .github/workflows/chanlun-gate.yml  # hosted Ubuntu CI: lake build + groundings
```

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

The Lean job typically takes ~5 minutes on a warm cache, ~25 minutes
cold. Groundings finish in ~30 seconds total.

---

## Cross-references

* The proof program these MWE files were developed in:
  [`codex-proof-workbench`](https://github.com/minustwo/codex-proof-workbench)
* Chan's published lessons (108课) are the source-of-truth for 中枢,
  走势类型, and the buy-sell-point geometry hooks used in the
  follow-up work.
* Mathlib v4.14.0 is the only library dependency.

---

## License

The theory PDFs (`chanlun.pdf`, `chanlun_zh.pdf`) are released into the
public domain per Klaus's authorial statement. The Lean formalization,
groundings, and CI workflow are MIT-licensed (see
[`LICENSE`](LICENSE) if present in the repo).
