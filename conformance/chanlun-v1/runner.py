"""Reference runner for the `chanlun-v1` conformance corpus.

What it does (in <100 lines of pure stdlib):

    1. Load `manifest.json` (the FROZEN spec pointer + per-fixture SHA-256 expectations).
    2. For each entry, load the fixture JSON, re-run the reference backend on `input`,
       canonicalize the output, recompute the three SHA-256s, and compare each one
       byte-for-byte against the manifest entry.
    3. Print PASS / FAIL per fixture; exit non-zero on ANY mismatch.

Conformance contract:

    *  SHA-equality is the law. A byte off -> FAIL. There is no fuzzy comparison,
       no "approximately equal", no float tolerance (the domain is integer-core).
    *  Any mismatch is surfaced with both the expected and the recomputed SHA so a
       Phase-3 multi-language implementor can see exactly which stage diverged.

A Phase-3 implementation (Python, JS/TS, Go, PineScript, ...) is conformant to
`chanlun-v1` iff its decomposition (over each fixture's `input`) canonicalizes to
the exact bytes whose SHA-256 equals `expected_sha256` for every fixture.
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
    """Canonical JSON bytes used for ALL SHA-256 computation."""
    return json.dumps(obj, **_CANON_KW).encode("utf-8")


def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


# Stage -> (input-shape interpretation, runner callable).
def run_stage(stage: str, inp):
    if stage == "normalize":
        return Nmod.normalize_N(inp)
    if stage == "fractal":
        return Fmod.extract_fractals(inp)
    if stage == "stroke":
        out, disp = Smod.strokes(inp["fractals"], inp["dmin"])
        return {"strokes": out, "dispositions": disp}
    if stage == "zhongshu":
        return Zmod.zhongshu(inp["elements"], inp["zone"])
    if stage == "trend_type":
        return Tmod.classify(inp)
    if stage == "pipeline":
        return P.run_full(inp["bars"], dmin=inp.get("dmin", P.DMIN), zone=inp.get("zone", "first3"))
    raise ValueError(f"unknown stage: {stage!r}")


def verify_one(entry: dict, fixture: dict) -> list:
    """Return the list of failure messages for one fixture (empty -> PASS)."""
    fails = []
    if entry["id"] != fixture["id"]:
        fails.append(f"id mismatch: manifest={entry['id']!r} fixture={fixture['id']!r}")
    if entry["stage"] != fixture["stage"]:
        fails.append(f"stage mismatch: manifest={entry['stage']!r} fixture={fixture['stage']!r}")
    stage = fixture["stage"]
    inp = fixture["input"]
    expected = fixture["expected"]

    in_canon = canon(inp)
    in_sha = sha256(in_canon)
    if in_sha != entry["input_sha256"]:
        fails.append(f"input_sha256 mismatch: manifest={entry['input_sha256']} recomputed={in_sha}")
    if in_sha != fixture["input_sha256"]:
        fails.append(
            f"input_sha256 mismatch (fixture vs recomputed): "
            f"fixture={fixture['input_sha256']} recomputed={in_sha}")

    # Re-run the reference backend and compare.
    try:
        actual = run_stage(stage, inp)
    except Exception as e:
        fails.append(f"backend raised: {type(e).__name__}: {e}")
        return fails

    exp_canon = canon(expected)
    act_canon = canon(actual)
    exp_sha = sha256(exp_canon)
    act_sha = sha256(act_canon)

    if act_sha != exp_sha:
        fails.append(
            f"output diverges: fixture-expected sha={exp_sha} backend-actual sha={act_sha}\n"
            f"  expected: {expected!r}\n"
            f"  actual:   {actual!r}")
    if exp_sha != entry["expected_sha256"]:
        fails.append(
            f"expected_sha256 mismatch: manifest={entry['expected_sha256']} fixture-recomputed={exp_sha}")

    fixture_sha = sha256(in_canon + b"|" + exp_canon)
    if fixture_sha != entry["fixture_sha256"]:
        fails.append(
            f"fixture_sha256 mismatch: manifest={entry['fixture_sha256']} recomputed={fixture_sha}")
    if fixture_sha != fixture["fixture_sha256"]:
        fails.append(
            f"fixture_sha256 mismatch (fixture vs recomputed): "
            f"fixture={fixture['fixture_sha256']} recomputed={fixture_sha}")

    return fails


def main(argv) -> int:
    manifest_path = _HERE / "manifest.json"
    if not manifest_path.exists():
        print(f"FAIL: manifest not found at {manifest_path}", file=sys.stderr)
        return 2
    manifest = json.loads(manifest_path.read_text("utf-8"))

    # Verify the corpus-level SHA.
    fixture_shas = [e["fixture_sha256"] for e in manifest["entries"]]
    corpus_sha = sha256(canon(fixture_shas))
    if corpus_sha != manifest["corpus_sha256"]:
        print(
            f"FAIL: corpus_sha256 mismatch: manifest={manifest['corpus_sha256']} "
            f"recomputed={corpus_sha}",
            file=sys.stderr,
        )
        return 2

    fail_count = pass_count = 0
    verbose = "--verbose" in argv or "-v" in argv
    print(f"chanlun-v1 corpus runner: verifying {manifest['count']} fixtures...")
    print(f"  corpus_sha256 = {manifest['corpus_sha256']}")
    for entry in manifest["entries"]:
        fixture_path = _HERE / entry["file"]
        try:
            fixture = json.loads(fixture_path.read_text("utf-8"))
        except Exception as e:
            print(f"  [FAIL] {entry['id']:60s} cannot read fixture {fixture_path}: {e}")
            fail_count += 1
            continue
        fails = verify_one(entry, fixture)
        if fails:
            fail_count += 1
            print(f"  [FAIL] {entry['id']:60s}")
            for msg in fails:
                for line in msg.splitlines():
                    print(f"           {line}")
        else:
            pass_count += 1
            if verbose:
                print(f"  [PASS] {entry['id']:60s}  sha={entry['fixture_sha256'][:12]}...")

    print()
    print(f"Result: {pass_count} PASS, {fail_count} FAIL")
    if fail_count:
        print("Conformance FAILED. Any byte-level divergence breaks the FROZEN spec.", file=sys.stderr)
        return 1
    print("Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
