"""Compare external full-pipeline projections against `chanlun-v1` fixtures.

This report is intentionally projection-based. It records which parts of an
external implementation's own object graph match the canonical full pipeline
and which parts are profile-local differences.
"""
from __future__ import annotations

import hashlib
import argparse
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "conformance" / "chanlun-v1"
REPORT = ROOT / "differential" / "PIPELINE_PROJECTION_REPORT.md"
sys.path.insert(0, str(ROOT / "differential"))

from external_backends import (  # noqa: E402
    ExternalBackendSkip,
    ProfileGap,
    chanpy_pipeline_projection,
    czsc_pypi_rs_projection,
)


PROJECTIONS = {
    "chanpy": chanpy_pipeline_projection,
    "czsc-pypi-rs": czsc_pypi_rs_projection,
}

FIELDS = ("normalized_bars", "fractals", "strokes", "zhongshu_centers")


def _canon(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha(obj) -> str:
    return hashlib.sha256(_canon(obj)).hexdigest()


def _short_sha(obj) -> str:
    return _sha(obj)[:12]


def _load_czsc_core_projection(path: Path) -> dict:
    return json.loads(path.read_text("utf-8"))


def _run_czsc_core_projection(timeout_seconds: int) -> dict:
    manifest = ROOT / "differential" / "czsc_core_probe" / "Cargo.toml"
    try:
        proc = subprocess.run(
            [
                "cargo",
                "run",
                "--quiet",
                "--manifest-path",
                str(manifest),
                "--",
                str(CORPUS),
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        raise ExternalBackendSkip(
            f"SKIP-LOUD: czsc-core cargo probe timed out after {timeout_seconds}s"
        ) from exc
    if proc.returncode != 0:
        raise ExternalBackendSkip(
            "SKIP-LOUD: czsc-core cargo probe failed: " + (proc.stderr.strip() or proc.stdout.strip())
        )
    return json.loads(proc.stdout)


def _append_projection_rows(rows, failures, backend: str, fixture_id: str, expected: dict, actual: dict) -> None:
    for field in FIELDS:
        exp = expected.get(field)
        act = actual.get(field)
        if act is None:
            rows.append((backend, fixture_id, field, "PROFILE-GAP", "-", "-", "field not emitted"))
            continue
        try:
            status = "equal" if _sha(exp) == _sha(act) else "profile_divergence"
            note = f"expected_n={len(exp)} actual_n={len(act)}"
            rows.append((backend, fixture_id, field, status, _short_sha(exp), _short_sha(act), note))
        except Exception as exc:
            rows.append((backend, fixture_id, field, "FAIL", "-", "-", f"{type(exc).__name__}: {exc}"))
            failures.append((backend, fixture_id, field, str(exc)))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--czsc-core-json",
        type=Path,
        help="optional JSON emitted by differential/czsc_core_probe",
    )
    parser.add_argument(
        "--include-czsc-core",
        action="store_true",
        help="run the optional Cargo-based czsc-core probe",
    )
    parser.add_argument(
        "--czsc-core-timeout",
        type=int,
        default=600,
        help="timeout in seconds for --include-czsc-core",
    )
    args = parser.parse_args(argv)

    manifest = json.loads((CORPUS / "manifest.json").read_text("utf-8"))
    rows = []
    failures = []
    external_projection_blobs = {}
    if args.czsc_core_json:
        external_projection_blobs["czsc-core"] = _load_czsc_core_projection(args.czsc_core_json)
    if args.include_czsc_core:
        try:
            external_projection_blobs["czsc-core"] = _run_czsc_core_projection(args.czsc_core_timeout)
        except ExternalBackendSkip as exc:
            for entry in manifest["entries"]:
                if entry["stage"] == "pipeline":
                    rows.append(("czsc-core", entry["id"], "*", "SKIP-LOUD", "-", "-", str(exc)))

    for backend, project in PROJECTIONS.items():
        for entry in manifest["entries"]:
            if entry["stage"] != "pipeline":
                continue
            fixture = json.loads((CORPUS / entry["file"]).read_text("utf-8"))
            try:
                actual = project(fixture["input"])
            except ExternalBackendSkip as exc:
                rows.append((backend, entry["id"], "*", "SKIP-LOUD", "-", "-", str(exc)))
                continue
            except ProfileGap as exc:
                rows.append((backend, entry["id"], "*", "PROFILE-GAP", "-", "-", str(exc)))
                continue
            except Exception as exc:
                rows.append((backend, entry["id"], "*", "FAIL", "-", "-", f"{type(exc).__name__}: {exc}"))
                failures.append((backend, entry["id"], str(exc)))
                continue
            _append_projection_rows(rows, failures, backend, entry["id"], fixture["expected"], actual)

    for backend, blob in external_projection_blobs.items():
        for entry in manifest["entries"]:
            if entry["stage"] != "pipeline":
                continue
            fixture = json.loads((CORPUS / entry["file"]).read_text("utf-8"))
            actual = blob.get(entry["id"])
            if actual is None:
                rows.append((backend, entry["id"], "*", "PROFILE-GAP", "-", "-", "fixture not emitted"))
                continue
            _append_projection_rows(rows, failures, backend, entry["id"], fixture["expected"], actual)

    lines = [
        "# Pipeline projection report",
        "",
        "Generated by `python3 differential/pipeline_projection_report.py`.",
        "This compares external full-pipeline object graphs against selected",
        "`chanlun-v1` pipeline fields without changing canonical geometry.",
        "",
        "| backend | fixture | field | status | expected_sha | actual_sha | note |",
        "|---|---|---|---:|---:|---:|---|",
    ]
    for row in rows:
        lines.append("| " + " | ".join(row) + " |")
    lines.extend([
        "",
        "Interpretation:",
        "",
        "- `equal` means the projected external field is byte-identical to the",
        "  canonical pipeline fixture field.",
        "- `profile_divergence` is expected when an external implementation uses a",
        "  different BI/ZS object graph or admissibility gate.",
        "- `SKIP-LOUD` means the optional external source/package is unavailable.",
        "- `czsc-core` rows appear only when `--czsc-core-json` or `--include-czsc-core` is used.",
        "- `czsc-pypi-rs` rows use the optional isolated PyPI release-profile",
        "  venv and represent rs_czsc's runtime object graph, not canonical status.",
        "",
    ])
    REPORT.write_text("\n".join(lines), "utf-8")
    print(f"wrote {REPORT}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
