# impl/ts - TypeScript backend for chanlun-v1

A faithful, pure-stdlib TypeScript port of the Chanlun pipeline reference
backend, conformant to the FROZEN `chanlun-v1` corpus byte-for-byte.

Chinese version: [README.zh.md](README.zh.md).

## What this is

`impl/ts/` is the second-language member of the Phase-3 multi-language Chanlun
pipeline. It is a port - not a re-derivation - of the Python reference at
`conformance/chanlun-v1/reference_backend/`. The six kernel-proven stages are
implemented in TypeScript with no runtime dependencies:

| Stage        | TypeScript module              | Python source                                                | Lean theorem               |
| ------------ | ------------------------------ | ------------------------------------------------------------ | -------------------------- |
| `normalize`  | `src/normalize.ts`             | `reference_backend/normalize.py`                             | `Chanlun.Normalize`        |
| `fractal`    | `src/fractal.ts`               | `reference_backend/fractal.py`                               | `Chanlun.Fractal`          |
| `stroke`     | `src/strokes.ts`               | `reference_backend/strokes.py`                               | `Chanlun.Stroke`           |
| `zhongshu`   | `src/zhongshu.ts`              | `reference_backend/zhongshu.py`                              | `Chanlun.Zhongshu`         |
| `trend_type` | `src/trend_type.ts`            | `reference_backend/trend_type.py`                            | `Chanlun.TrendType`        |
| `pipeline`   | `src/pipeline.ts`              | `reference_backend/pipeline.py`                              | composed pipeline contract |

The six stages outside `chanlun-v1` (walk decomposition, three-class buy/sell,
divergence, zhongshu extension, level recursion, segment) are deliberately not
ported here - they will come with `chanlun-v2` / `chanlun-v3` corpora.

## The lineage chain

The trust chain this backend extends is:

```
chanlun.md (Definitions 2-5, lessons 17/20/24)
  -> lean/Chanlun/*.lean (kernel-verified theorems, sorry-free)
  -> conformance/chanlun-v1/reference_backend/*.py (standalone Python oracles)
  -> impl/ts/src/*.ts  ==SHA==>  conformance/chanlun-v1/fixtures/*.json
```

Each link is checked: the Lean kernel checks the proofs; the Python oracle is
exercised by `grounding/` over hundreds of thousands of random sequences plus
§15 mutants; the corpus is byte-frozen with `corpus_sha256`; this TS backend
must reproduce every fixture's `expected_sha256` exactly.

## The §15 SHA-equality law

> SHA-256 of the canonical JSON of every stage's output must equal the
> `expected_sha256` for the corresponding fixture. A single byte off = FAIL,
> non-zero exit. No fuzzy match, no float tolerance, no "approximately equal".

A genuinely-unrepresentable fixture is NAMED as an OPEN residue
(`[chanlun_v1_ts_<stage>_<fixture>_OPEN]`) and resolved in a follow-up, never
silently skipped. The CI gate is the only arbiter - never a local verbal claim.

## How to run locally

```bash
cd impl/ts
npm ci --omit=optional   # installs only typescript + @types/node devDeps
npx tsc                  # emits dist/
node dist/check.js       # runs the 48-fixture harness; exits 0 iff all pass
```

Expected output:

```
chanlun-v1 phase-3 check, backend = impl/ts
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
```

`npm run check` is a shortcut for the `tsc && node dist/check.js` cycle.

## CI

The `conformance-ts` job in `.github/workflows/chanlun-gate.yml` runs this
exact cycle on hosted Ubuntu (Node 20). Green CI is the only proof of
conformance.

## Design notes

- **No runtime dependencies.** `package.json` declares only `typescript` and
  `@types/node` as devDeps. The runtime uses Node's built-in `node:crypto`
  (for SHA-256) and `node:fs/promises` (for fixture I/O). Nothing else.
- **Integer-core.** The corpus contains only integer bars, fractals, prices,
  and zones. `canonical.ts` rejects non-integer numbers - by design, to
  prevent a silent float drift away from the Python oracle.
- **Canonical JSON.** `src/canonical.ts` mirrors Python's
  `json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True)`
  exactly: keys sorted lexicographically, no whitespace, non-ASCII escaped as
  `\uXXXX`. The corpus's `corpus_sha256` is computed under this same encoding,
  so reproducing it requires matching the encoding byte-for-byte.
- **Pure functions, no shared state.** Each stage is a stateless function over
  plain JSON objects, matching the reference's data-only protocol.

## Files

```
impl/ts/
  package.json          - devDeps (typescript, @types/node) only
  tsconfig.json         - ES2022 / strict / no source maps
  check.ts              - the 48-fixture conformance harness (entry point)
  src/
    types.ts            - shared interface types (Bar, Fractal, Stroke, ...)
    normalize.ts        - Algorithm N (Appendix A inclusion-normalization)
    fractal.ts          - Def-3 top/bottom classifier
    strokes.ts          - Def-4 + Lemma 2 leftmost-greedy stroke walk
    zhongshu.ts         - >=3-overlap center decomposition (first3 / all)
    trend_type.ts       - lesson 17 consolidation / trend classifier
    pipeline.ts         - bars -> trend_type end-to-end pipeline
    canonical.ts        - Python-compatible canonical JSON encoder
```
