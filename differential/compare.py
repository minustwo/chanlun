"""Compare a backend against the frozen `chanlun-v1` corpus.

The script deliberately ships only self-contained backends. Integrations for
chan.py, czsc, or product workbenches should be added as explicit modules once
their output wire shape is pinned. Until then, they are declared profiles, not
trusted geometry.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "conformance" / "chanlun-v1"
sys.path.insert(0, str(CORPUS))

import runner as corpus_runner  # noqa: E402
from external_backends import EXTERNAL_BACKENDS, ExternalBackendSkip, ProfileGap  # noqa: E402


def _canon(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha(obj) -> str:
    return hashlib.sha256(_canon(obj)).hexdigest()


def backend_canonical(stage: str, inp, fixture: dict):
    return corpus_runner.run_stage(stage, inp)


def backend_fixture_replay(stage: str, inp, fixture: dict):
    return fixture["expected"]


BACKENDS = {
    "canonical": backend_canonical,
    "fixture-replay": backend_fixture_replay,
}
BACKENDS.update(EXTERNAL_BACKENDS)


def compare_backend(name: str, *, stage_filter: str | None = None, json_output: bool = False) -> int:
    if name not in BACKENDS:
        print(
            f"SKIP-LOUD: backend {name!r} is not wired. Add an explicit adapter before comparison.",
            file=sys.stderr,
        )
        return 2
    backend = BACKENDS[name]

    manifest = json.loads((CORPUS / "manifest.json").read_text("utf-8"))
    total = equal = unknown = raised = known_profile_divergence = skipped = 0
    failures = []
    known = []
    skip_reasons = []
    for entry in manifest["entries"]:
        if stage_filter and entry["stage"] != stage_filter:
            continue
        total += 1
        fixture = json.loads((CORPUS / entry["file"]).read_text("utf-8"))
        try:
            actual = backend(fixture["stage"], fixture["input"], fixture)
        except ExternalBackendSkip as exc:
            skipped += 1
            skip_reasons.append(str(exc))
            continue
        except ProfileGap as exc:
            known_profile_divergence += 1
            known.append({
                "id": entry["id"],
                "class": "known_profile_divergence",
                "reason": str(exc),
            })
            continue
        except Exception as exc:  # pragma: no cover - exercised by future external backends
            raised += 1
            failures.append({
                "id": entry["id"],
                "class": "unknown_divergence",
                "reason": f"backend raised {type(exc).__name__}: {exc}",
            })
            continue
        actual_sha = _sha(actual)
        if actual_sha == entry["expected_sha256"]:
            equal += 1
        else:
            if name in EXTERNAL_BACKENDS:
                known_profile_divergence += 1
                known.append({
                    "id": entry["id"],
                    "class": "known_profile_divergence",
                    "reason": "external profile output differs from canonical corpus",
                    "expected_sha256": entry["expected_sha256"],
                    "actual_sha256": actual_sha,
                })
                continue
            unknown += 1
            failures.append({
                "id": entry["id"],
                "class": "unknown_divergence",
                "expected_sha256": entry["expected_sha256"],
                "actual_sha256": actual_sha,
            })

    summary = {
        "backend": name,
        "stage": stage_filter or "*",
        "total": total,
        "equal": equal,
        "known_profile_divergence": known_profile_divergence,
        "unknown_divergence": unknown + raised,
        "skipped": skipped,
        "known": known,
        "failures": failures,
    }

    if json_output:
        print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
    else:
        print(
            f"differential: backend={name} stage={summary['stage']} "
            f"equal={equal}/{total} known_profile_divergence={known_profile_divergence} "
            f"unknown_divergence={unknown + raised} skipped={skipped}"
        )
        for reason in sorted(set(skip_reasons))[:3]:
            print(f"  {reason}")
        for item in known[:10]:
            print(f"  {item['class']}: {item['id']} {item.get('reason', '')}")
        for failure in failures[:10]:
            print(f"  {failure['class']}: {failure['id']} {failure.get('reason', '')}")

    return 1 if failures else (2 if skipped == total and total else 0)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", default="canonical", help=f"one of {sorted(BACKENDS)}")
    parser.add_argument("--stage", default=None, help="optional corpus stage filter")
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    args = parser.parse_args(argv)
    return compare_backend(args.backend, stage_filter=args.stage, json_output=args.json)


if __name__ == "__main__":
    raise SystemExit(main())
