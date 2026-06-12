# chanlun-v1 C# / .NET backend

A faithful, integer-core port of the chanlun-v1 pipeline to C# / .NET 8, with a
local conformance harness that checks all 48 fixtures against the FROZEN
`conformance/chanlun-v1` corpus byte-for-byte (SHA-256 equality).

SHA-equality is the law. A byte off = FAIL. There is no fuzzy comparison, no
"approximately equal", no float tolerance — the chanlun-v1 corpus is
integer-core throughout.

## Lineage

The C# port mirrors the pure-Python reference at
`conformance/chanlun-v1/reference_backend/` and the existing Go port at
`impl/go/internal/chanlun/`. The Python reference is the GROUND TRUTH; on any
divergence between `impl/ts`, `impl/go`, and this `impl/csharp`, the Python
reference wins.

## Layout

```
impl/csharp/
  Chanlun.sln                            # solution
  src/
    Chanlun/                             # the library
      Chanlun.csproj                     # netstandard-friendly net8.0 lib
      Types.cs                           # Bar, Fractal, Stroke, Element, Center, PipelineResult
      Canonical.cs                       # canonical JSON encoder + SHA-256 + decoder
      Normalize.cs                       # Algorithm N (包含处理 / inclusion-normalization)
      Fractal.cs                         # Def-3 fractal classifier
      Strokes.cs                         # Def-4 + Lemma 2 stroke greedy
      Zhongshu.cs                        # 走势中枢 decomposition (zone gate: first3 / all)
      TrendType.cs                       # 走势类型 classifier (consolidation/trend_up/trend_down/mixed/none)
      Pipeline.cs                        # end-to-end pipeline + stage dispatch
    Chanlun.Check/                       # the conformance harness
      Chanlun.Check.csproj               # net8.0 exe
      Program.cs                         # main: load manifest, run each stage, compare SHA-256
```

## Build

```
cd impl/csharp
dotnet restore
dotnet build -c Release --no-restore
```

## Run the conformance harness

```
cd impl/csharp
dotnet run -c Release --no-build --project src/Chanlun.Check/Chanlun.Check.csproj
```

The harness walks up from the working directory looking for
`conformance/chanlun-v1/manifest.json`, so it also works when invoked from the
repo root.

Expected output:

```
chanlun-v1 C# conformance check: 48 fixtures
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.
```

Exit code is 0 on full pass, 1 on any byte-level divergence.

## Canonical JSON (the byte-locked part)

The SHA-256 inputs are computed over canonical JSON bytes that match Python's
`json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)`
byte-for-byte. `System.Text.Json` does NOT sort keys lexicographically (it
preserves insertion order) and its escape policy differs from Python's, so we
roll a custom emitter over a typed `Value` tree (Canonical.cs).

Specifically:

* Object keys are sorted by `StringComparer.Ordinal` (= Python's str sort over
  ASCII = lexicographic UTF-8 byte order). All keys in the chanlun-v1 corpus
  are ASCII.
* Separators are `,` and `:` with no whitespace.
* Strings escape `\\`, `\"`, `\b`, `\f`, `\n`, `\r`, `\t` as shortcuts; control
  chars and non-ASCII via `\uXXXX` (surrogate pairs for non-BMP) — exactly like
  Python `ensure_ascii=True`.
* Numbers are emitted as `long` integers using `InvariantCulture` to avoid
  locale-specific thousand separators or decimal points.
* The corpus is integer-core: the decoder rejects any non-integer number to
  fail loudly rather than silently downconvert.

## Conformance status

* All 48 fixtures pass byte-identical SHA-256 against the FROZEN chanlun-v1
  spec (verified locally and in CI via the `conformance-csharp` job in
  `.github/workflows/chanlun-gate.yml`).
* No runtime dependencies (System.Text.Json is part of the BCL).

## Why .NET 8

LTS, stable, and the version that `actions/setup-dotnet@v4` resolves with
`dotnet-version: '8.0.x'` in the gate.
