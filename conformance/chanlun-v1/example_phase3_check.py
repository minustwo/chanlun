"""Example: a Phase-3 implementation conforming check (one-pager template).

A Phase-3 multi-language implementor (Python, JS/TS, Go, PineScript, ...) follows this
shape to validate their implementation against chanlun-v1.

    1. Build their own Chanlun pipeline (normalize -> fractal -> stroke -> zhongshu -> trend_type).
    2. For each fixture in `manifest.json`, run their pipeline on `input`.
    3. Canonicalize the output via the SAME canonical-JSON rules
       (sort_keys=True, separators=(',', ':'), ensure_ascii=True).
    4. SHA-256(canonical_output) == fixture's expected_sha256 -> PASS, else FAIL.

This script is a tiny end-to-end example with two backends:

    *  ``reference``  - the in-repo Python reference (must pass every fixture by construction).
    *  ``alt``        - a deliberately-different (but byte-equivalent) Python implementation that
                         shows what a Phase-3 implementor needs to do. A "hello world" alternative
                         that delegates to the reference for each stage: this should pass.

A REAL alternative implementation - e.g. Go's pure-stdlib port - replaces ``alt`` with the bridge
to that language. The protocol stays the same.

Run:  python3 conformance/chanlun-v1/example_phase3_check.py [reference | alt]
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from reference_backend import pipeline as P  # noqa: E402
from reference_backend import normalize as Nmod  # noqa: E402
from reference_backend import fractal as Fmod  # noqa: E402
from reference_backend import strokes as Smod  # noqa: E402
from reference_backend import zhongshu as Zmod  # noqa: E402
from reference_backend import trend_type as Tmod  # noqa: E402


_CANON_KW = dict(sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def canon(obj) -> bytes:
    return json.dumps(obj, **_CANON_KW).encode("utf-8")


def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


# ----------------------------------------------------------------------------
# Backend (reference): direct call to the in-repo Python.
# ----------------------------------------------------------------------------
def backend_reference(stage: str, inp):
    if stage == "normalize":   return Nmod.normalize_N(inp)
    if stage == "fractal":     return Fmod.extract_fractals(inp)
    if stage == "stroke":
        out, disp = Smod.strokes(inp["fractals"], inp["dmin"])
        return {"strokes": out, "dispositions": disp}
    if stage == "zhongshu":    return Zmod.zhongshu(inp["elements"], inp["zone"])
    if stage == "trend_type":  return Tmod.classify(inp)
    if stage == "pipeline":    return P.run_full(inp["bars"], dmin=inp.get("dmin", P.DMIN), zone=inp.get("zone", "first3"))
    raise ValueError(f"unknown stage: {stage!r}")


# ----------------------------------------------------------------------------
# Backend (alt): a stand-in for a real Phase-3 implementation. Here we just
# delegate to the reference, but a real port would have its own implementation.
# A naive ALT might wrap each stage in a small detour to show the pattern.
# ----------------------------------------------------------------------------
def backend_alt(stage: str, inp):
    # The pattern: a "hello world" Phase-3 implementation does each stage in its
    # own (potentially native) code path. Here we round-trip through JSON to
    # demonstrate the protocol is data-only (no Python objects cross the boundary).
    json_inp = json.loads(json.dumps(inp))
    return backend_reference(stage, json_inp)


BACKENDS = {"reference": backend_reference, "alt": backend_alt}


def main(argv) -> int:
    name = argv[0] if argv else "reference"
    if name not in BACKENDS:
        print(f"unknown backend: {name!r}. Choose from {sorted(BACKENDS)}", file=sys.stderr)
        return 2
    backend = BACKENDS[name]

    manifest = json.loads((_HERE / "manifest.json").read_text("utf-8"))
    fails = 0
    print(f"chanlun-v1 phase-3 check with backend = {name}")
    print(f"  corpus_sha256 = {manifest['corpus_sha256']}")
    for entry in manifest["entries"]:
        fixture = json.loads((_HERE / entry["file"]).read_text("utf-8"))
        try:
            actual = backend(fixture["stage"], fixture["input"])
        except Exception as e:
            print(f"  [FAIL] {entry['id']:60s} backend raised {type(e).__name__}: {e}")
            fails += 1
            continue
        act_sha = sha256(canon(actual))
        if act_sha != entry["expected_sha256"]:
            print(f"  [FAIL] {entry['id']:60s} actual sha={act_sha[:12]}... expected sha={entry['expected_sha256'][:12]}...")
            fails += 1
    total = manifest["count"]
    print()
    print(f"Result: {total - fails} PASS, {fails} FAIL")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
