# Chanlun-v1 — Java conformance backend

A faithful pure-Java port of the chanlun-v1 reference backend
(`conformance/chanlun-v1/reference_backend/*.py`), passing every fixture
in the frozen `chanlun-v1` corpus byte-for-byte under SHA-equality.

## What this is

The corpus `conformance/chanlun-v1` is the frozen multi-language
conformance spec for the Chanlun pipeline (48 fixtures × 6 stages,
byte-locked SHA-256;
`corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`).
An implementation in any language is conformant iff its decomposition
over each fixture's `input` canonicalizes to the exact bytes whose
SHA-256 equals the fixture's `expected_sha256`.

This module is that implementation in Java. It is:

* **A faithful port**, not a re-derivation. Each `src/main/java/com/minustwo/chanlun/*.java`
  file mirrors the corresponding `reference_backend/*.py` and
  `impl/go/internal/chanlun/*.go` line-by-line so that the only place
  divergence can creep in is canonical-JSON byte encoding (see Canonical-JSON below).
* **Zero runtime dependencies** — pure Java + the standard library.
  The hand-rolled JSON parser + canonical emitter avoids the
  insertion-order / `ensure_ascii` quirks that would otherwise need
  fragile Jackson/Gson configuration.
* **Integer-core**, like the Python reference. Floats in input fixtures
  are explicitly rejected by the decoder rather than silently coerced.
* **Six stages, exactly the six in the corpus**: `normalize`, `fractal`,
  `stroke`, `zhongshu`, `trend_type`, `pipeline`.

## Layout

```
impl/java/
  pom.xml                                          Maven build (Java 17)
  src/main/java/com/minustwo/chanlun/
    Types.java                                     Value tree + records
    Canonical.java                                 JSON parser + canonical emitter + SHA-256
    Normalize.java                                 Algorithm N (chanlun.pdf Appendix A)
    Fractals.java                                  Def-3 (分型) classifier
    Strokes.java                                   Def-4 + Lemma 2 笔 greedy
    Zhongshu.java                                  走势中枢 decomposition
    TrendType.java                                 走势类型 classifier
    Pipeline.java                                  End-to-end run_full + stage dispatcher
  src/main/java/com/minustwo/chanlun/check/
    Check.java                                     Conformance harness (main)
```

## Build

```bash
cd impl/java
mvn -B -DskipTests package
```

This produces `target/chanlun-check.jar`, a self-contained executable jar
(no shaded deps because there are no runtime deps).

## Run

```bash
java -jar target/chanlun-check.jar
```

The harness walks up the directory tree from the cwd looking for
`conformance/chanlun-v1/manifest.json`, so it works from either
`impl/java/` or the repo root. Expected output:

```
chanlun-v1 Java conformance check: 48 fixtures
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.
```

Exit code 0 = all 48 fixtures pass byte-for-byte; non-zero = at least one
divergence (the harness exits non-zero on ANY byte-level mismatch).

## Canonical-JSON

The Python reference uses

```python
json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
```

The Java canonical emitter (`Canonical.canonical`) reproduces this
byte-for-byte:

* **Sorted object keys** — lexicographic / code-point order; matches
  Python for the all-ASCII keys in the corpus.
* **No whitespace** — `(",", ":")` separators reproduced exactly.
* **ASCII-only output** — every code point >= 0x7f is escaped as
  `\uXXXX`; code points beyond the BMP become a UTF-16 surrogate pair.
* **Integer-core** — the parser rejects any number containing `.`, `e`,
  or `E`. A stray float in input data is an honest error, never silently
  truncated.

These three guarantees are what makes the SHA-256 comparison meaningful.
A byte off is a FAIL.

## Status

* 48 / 48 fixtures PASS, SHA-256-equal byte-for-byte against the
  Python reference and the existing `impl/ts` / `impl/go` ports.
* Verified locally with OpenJDK 21 + Maven 3.9.
* CI: `conformance-java` job in `.github/workflows/chanlun-gate.yml`
  runs the same `java -jar target/chanlun-check.jar` on every PR
  (Temurin 21, 5-minute timeout — same budget as the TS / Go gates).
