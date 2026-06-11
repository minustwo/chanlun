# Chanlun-v1 — Go conformance backend

A faithful pure-stdlib Go port of the chanlun-v1 reference backend
(`conformance/chanlun-v1/reference_backend/*.py`), passing every fixture in the
FROZEN `chanlun-v1` corpus byte-for-byte under the §15 SHA-equality law.

## What this is

The corpus `conformance/chanlun-v1` is the FROZEN multi-language conformance
spec for the Chanlun pipeline (48 fixtures × 6 stages, byte-locked SHA-256;
`corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`).
A Phase-3 implementation in any language is conformant iff its decomposition
over each fixture's `input` canonicalizes to the exact bytes whose SHA-256
equals the fixture's `expected_sha256`.

This module is that Phase-3 implementation in Go. It is:

* **A faithful port**, not a re-derivation. Each `internal/chanlun/*.go`
  file mirrors the corresponding `reference_backend/*.py` line-by-line so
  that the only place divergence can creep in is canonical-JSON byte
  encoding (the load-bearing detail; see below).
* **Pure stdlib**, zero third-party dependencies (`go.mod` lists none).
* **Integer-core**, like the Python reference. Floats in input fixtures
  would be a NAMED structural residue and the decoder rejects them.
* **Six stages, exactly the six in the corpus**: `normalize`, `fractal`,
  `stroke`, `zhongshu`, `trend_type`, `pipeline`. Out-of-corpus stages
  (segment, level-recursion, walk-decomposition) are intentionally NOT
  ported here — they are part of the Lean library, not the conformance
  corpus.

## Run

From the repo root:

```bash
cd impl/go
go build ./...
go run ./cmd/check
```

Expected output:

```
chanlun-v1 Go conformance check: 48 fixtures
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.
```

Build requires Go 1.22 or newer. There are no other build prerequisites.

## Layout

```
impl/go/
  go.mod                                    # module github.com/minustwo/chanlun/impl/go (Go 1.22)
  cmd/check/main.go                         # the conformance harness (loads manifest -> runs each stage -> compares SHA-256)
  internal/chanlun/
    canon.go                                # canonical JSON encoder + SHA-256
    decode.go                               # JSON -> typed Value tree (int-preserving)
    normalize.go                            # Algorithm N (containment normalization, Appendix A)
    fractal.go                              # Def-3 top/bottom classifier
    strokes.go                              # Def-4 + Lemma 2 stroke greedy
    zhongshu.go                             # zhongshu (>= 3 overlap) decomposition with zone gate
    trend_type.go                           # consolidation / trend_up / trend_down / mixed / none
    pipeline.go                             # end-to-end run_full
    stage.go                                # stage dispatch (mirrors example_phase3_check.py)
  README.md                                 # this file
  README.zh.md                              # Chinese version
```

## Stage map (Go ↔ Python)

| Stage      | Go file                          | Python file                          |
|------------|----------------------------------|--------------------------------------|
| normalize  | `internal/chanlun/normalize.go`  | `reference_backend/normalize.py`     |
| fractal    | `internal/chanlun/fractal.go`    | `reference_backend/fractal.py`       |
| stroke     | `internal/chanlun/strokes.go`    | `reference_backend/strokes.py`       |
| zhongshu   | `internal/chanlun/zhongshu.go`   | `reference_backend/zhongshu.py`      |
| trend_type | `internal/chanlun/trend_type.go` | `reference_backend/trend_type.py`    |
| pipeline   | `internal/chanlun/pipeline.go`   | `reference_backend/pipeline.py`      |

## Canonical-JSON choice (the load-bearing detail)

The §15 SHA-equality law is computed over the canonical JSON bytes Python
produces with:

```python
json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
```

Go's stdlib `encoding/json` does NOT reproduce these bytes by default:
keys are emitted in map-insertion (or unspecified) order, and there is no
`ensure_ascii=True` equivalent. So we ship a small canonical emitter
(`internal/chanlun/canon.go`) over a typed `Value` tree, with these
behaviours:

1. **Sorted keys** — object keys are sorted by Unicode code-point order on
   the raw string key. All keys in the chanlun-v1 corpus are ASCII, so
   this coincides with lexicographic byte order, which is what Python's
   `sort_keys=True` does for `str` keys.
2. **No whitespace** — `,` and `:` are emitted with no space on either
   side (matching `separators=(",", ":")`).
3. **`ensure_ascii=True`** — every code point >= 0x7f is escaped as
   `\uXXXX`. Code points beyond the BMP use a UTF-16 surrogate pair (this
   matches Python's `json.dumps` behaviour exactly). Standard short
   escapes (`\"`, `\\`, `\b`, `\f`, `\n`, `\r`, `\t`) are used; other
   control characters (< 0x20) are emitted as `\u00XX`.
4. **Integers stay integers** — the JSON decoder uses
   `json.Decoder.UseNumber()` and rejects any token containing `.`, `e`,
   or `E`. The corpus is integer-core; silently downcasting an unexpected
   float into an `int64` (or up-casting an `int` into a `float64` and
   emitting it as `123.0`) would silently break SHA equality.

The result: over the chanlun-v1 corpus, each stage's emit matches the
Python reference's canonical bytes exactly — every one of the 48
`expected_sha256`s recomputes correctly, and the harness's corpus-level
recomputation of `corpus_sha256` reproduces the manifest value
`df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`.

If a future fixture introduces values outside this ASCII-keyed
integer-core domain (e.g. UTF-8 keys with multi-byte code points, or
non-integer numbers), the canonical encoder will still emit Python-faithful
bytes for strings (via the explicit `\uXXXX` path with surrogate handling),
but a NAMED residue would have to be opened for non-integer numbers since
the corpus contract forbids them today.

## Lineage

The §15 SHA-equality law and the FROZEN-corpus discipline come from the
proof-program upstream (`minustwo/codex-proof-workbench`). The reference
Python backend at `conformance/chanlun-v1/reference_backend/` is the
single source of truth for stage semantics; this Go port reproduces those
semantics exactly. No backend logic is invented here — every divergence
from the Python is restricted to the canonical-JSON emit layer, and the
SHA-equality gate is the regression test that catches any drift.

## CI

The CI job that runs this harness on every push / PR is
`conformance-go` in `.github/workflows/chanlun-gate.yml`. It uses
`actions/setup-go@v5` with Go 1.22 and runs:

```bash
cd impl/go
go build ./...
go run ./cmd/check
```

Non-zero exit fails the gate. SHA-equality is the law: a byte off is FAIL,
never silently skipped.
