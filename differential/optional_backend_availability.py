"""Check optional external backend availability without running heavy builds."""
from __future__ import annotations

import argparse
import importlib.util
import os
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "differential" / "OPTIONAL_BACKENDS_REPORT.md"
CZSC_PYPI_VENV = Path("/tmp/chanlun-externals/czsc-pypi-venv")
CZSC_PYPI_SYSTEM_VENV = Path("/tmp/chanlun-externals/czsc-pypi-system-venv")


def _text(value) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def _run(cmd: list[str], *, timeout: int = 30) -> tuple[str, str]:
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
    except FileNotFoundError as exc:
        return "SKIP-LOUD", f"missing executable: {exc.filename}"
    except subprocess.TimeoutExpired:
        return "SKIP-LOUD", f"timed out after {timeout}s: {' '.join(cmd)}"
    out = (proc.stdout + proc.stderr).strip()
    if proc.returncode == 0:
        return "OK", out.splitlines()[-1] if out else "ok"
    for line in out.splitlines():
        if "ModuleNotFoundError:" in line:
            return "SKIP-LOUD", line.strip()
        if "no matching package" in line or "required by package" in line:
            return "SKIP-LOUD", line.strip()
    lines = out.splitlines()
    return "SKIP-LOUD", lines[-1] if lines else f"exit {proc.returncode}"


def _chanpy_row() -> tuple[str, str, str]:
    root = Path(os.environ.get("CHANPY_ROOT", "/tmp/chanlun-externals/chan.py"))
    if (root / "Chan.py").exists():
        return ("chanpy source", "OK", str(root))
    return ("chanpy source", "SKIP-LOUD", "set CHANPY_ROOT or run fetch_external_sources.py chanpy")


def _czsc_native_row() -> tuple[str, str, str]:
    try:
        spec = importlib.util.find_spec("czsc._native")
    except Exception as exc:
        return ("czsc._native import", "SKIP-LOUD", str(exc))
    if spec is None:
        return ("czsc._native import", "SKIP-LOUD", "module not importable")
    return ("czsc._native import", "OK", str(spec.origin))


def _module_row(check: str, module: str) -> tuple[str, str, str]:
    try:
        spec = importlib.util.find_spec(module)
    except Exception as exc:
        return (check, "SKIP-LOUD", str(exc))
    if spec is None:
        return (check, "SKIP-LOUD", "module not importable")
    return (check, "OK", str(spec.origin))


def _czsc_pypi_venv_row(label: str, venv: Path) -> tuple[str, str, str]:
    python = venv / "bin" / "python"
    if not python.exists():
        return (label, "SKIP-LOUD", "run install_czsc_pypi_profile.py")
    return (label, "OK", str(venv))


def _czsc_pypi_venv_import_row(label: str, venv: Path) -> tuple[str, str, str]:
    python = venv / "bin" / "python"
    if not python.exists():
        return (label, "SKIP-LOUD", "run install_czsc_pypi_profile.py")
    status, note = _run([
        str(python),
        "-c",
        "import rs_czsc; print('rs_czsc import OK')",
    ])
    return (label, status, note)


def _czsc_core_metadata_row() -> tuple[str, str, str]:
    status, note = _run([
        "cargo",
        "metadata",
        "--manifest-path",
        "differential/czsc_core_probe/Cargo.toml",
        "--no-deps",
        "--format-version",
        "1",
    ])
    if status == "OK":
        note = "Cargo manifest resolves without fetching dependencies"
    return ("czsc-core probe metadata", status, note)


def _czsc_core_cache_row() -> tuple[str, str, str]:
    status, note = _run([
        "cargo",
        "fetch",
        "--manifest-path",
        "differential/czsc_core_probe/Cargo.toml",
        "--offline",
        "-v",
    ])
    return ("czsc-core offline cache", status, note)


def _czsc_core_online_fetch_row(timeout: int) -> tuple[str, str, str]:
    try:
        proc = subprocess.run(
            [
                "cargo",
                "fetch",
                "--manifest-path",
                "differential/czsc_core_probe/Cargo.toml",
                "-v",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout,
            env={
                **os.environ,
                "CARGO_REGISTRIES_CRATES_IO_PROTOCOL": "sparse",
                "CARGO_HTTP_MULTIPLEXING": "false",
                "CARGO_HTTP_TIMEOUT": "30",
            },
        )
    except subprocess.TimeoutExpired as exc:
        tail = (_text(exc.stdout) + _text(exc.stderr)).strip().splitlines()
        note = tail[-1] if tail else "no output"
        return ("czsc-core online fetch", "SKIP-LOUD", f"timed out after {timeout}s; last output: {note}")
    out = (proc.stdout + proc.stderr).strip()
    if proc.returncode == 0:
        return ("czsc-core online fetch", "OK", "cargo fetch completed")
    return ("czsc-core online fetch", "SKIP-LOUD", out.splitlines()[0] if out else f"exit {proc.returncode}")


def _czsc_pypi_download_row(timeout: int) -> tuple[str, str, str]:
    wheel_dir = Path("/tmp/chanlun-externals/pypi-wheels")
    wheel_dir.mkdir(parents=True, exist_ok=True)
    wheel = wheel_dir / "rs_czsc-0.1.26.post260402-cp39-abi3-macosx_11_0_arm64.whl"
    url = (
        "https://files.pythonhosted.org/packages/a2/f3/989b03585139a1c63559a75d3d43e8a350913f78b9c04f4c5a621f36cb7b/"
        "rs_czsc-0.1.26.post260402-cp39-abi3-macosx_11_0_arm64.whl"
    )
    status, note = _run([
        "curl",
        "-L",
        "-C",
        "-",
        "--retry",
        "5",
        "--retry-delay",
        "2",
        "--connect-timeout",
        "20",
        "--max-time",
        str(timeout),
        "-o",
        str(wheel),
        url,
    ], timeout=timeout + 10)
    if wheel.exists():
        size = wheel.stat().st_size
        if size == 12_333_247:
            return ("rs-czsc wheel download", "OK", f"{wheel} ({size} bytes)")
        return ("rs-czsc wheel download", "SKIP-LOUD", f"partial wheel at {wheel} ({size}/12333247 bytes)")
    return ("rs-czsc wheel download", status, note)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--probe-czsc-core-online",
        action="store_true",
        help="attempt networked cargo fetch for the optional czsc-core probe",
    )
    parser.add_argument(
        "--probe-czsc-pypi-download",
        action="store_true",
        help="attempt PyPI wheel download for rs-czsc",
    )
    parser.add_argument("--online-timeout", type=int, default=180)
    args = parser.parse_args(argv)

    rows = [
        _chanpy_row(),
        _czsc_native_row(),
        _module_row("czsc PyPI import", "czsc"),
        _module_row("rs_czsc import", "rs_czsc"),
        _czsc_pypi_venv_row("czsc PyPI venv", CZSC_PYPI_VENV),
        _czsc_pypi_venv_import_row("czsc PyPI venv rs_czsc import", CZSC_PYPI_VENV),
        _czsc_pypi_venv_row("czsc PyPI system-site venv", CZSC_PYPI_SYSTEM_VENV),
        _czsc_pypi_venv_import_row("czsc PyPI system-site rs_czsc import", CZSC_PYPI_SYSTEM_VENV),
        _czsc_core_metadata_row(),
        _czsc_core_cache_row(),
    ]
    if args.probe_czsc_core_online:
        rows.append(_czsc_core_online_fetch_row(args.online_timeout))
    if args.probe_czsc_pypi_download:
        rows.append(_czsc_pypi_download_row(args.online_timeout))
    lines = [
        "# Optional backend availability report",
        "",
        "Generated by `python3 differential/optional_backend_availability.py`.",
        "This report checks whether optional external runtime comparisons can run",
        "in the current environment. SKIP-LOUD is an explicit residual risk, not a pass.",
        "",
        "| check | status | note |",
        "|---|---:|---|",
    ]
    for row in rows:
        lines.append("| " + " | ".join(row) + " |")
    lines.extend([
        "",
        "Interpretation:",
        "",
        "- `chanpy source` being OK enables `chanpy` runtime differentials.",
        "- `czsc._native import` being OK enables the Python native backend.",
        "- `czsc PyPI import` and `rs_czsc import` being OK enable the PyPI 0.10 release profile.",
        "- `czsc PyPI ... rs_czsc import` checks the isolated release-profile",
        "  venv created by `install_czsc_pypi_profile.py`; missing import deps",
        "  remain SKIP-LOUD. The system-site variant is for runtime probing only.",
        "- `czsc-core offline cache` being OK means the Rust probe can build without",
        "  touching the network; otherwise first build still depends on crates.io.",
        "- `czsc-core online fetch` is optional and only appears when",
        "  `--probe-czsc-core-online` is passed.",
        "- `rs-czsc wheel download` is optional and only appears when",
        "  `--probe-czsc-pypi-download` is passed.",
        "",
    ])
    REPORT.write_text("\n".join(lines), "utf-8")
    print(f"wrote {REPORT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
