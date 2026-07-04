"""Install the optional PyPI `czsc 0.10.x` release profile into /tmp.

This is not part of the default gate. It exists so the release profile can be
made runnable without changing the repository environment:

    python3 differential/install_czsc_pypi_profile.py
"""
from __future__ import annotations

import subprocess
import sys
import argparse
from pathlib import Path


ROOT = Path("/tmp/chanlun-externals")
WHEELS = ROOT / "pypi-wheels"
VENV = ROOT / "czsc-pypi-venv"
SYSTEM_SITE_VENV = ROOT / "czsc-pypi-system-venv"

CZSC_WHEEL = (
    "czsc-0.10.12-py3-none-any.whl",
    "https://files.pythonhosted.org/packages/02/3d/2f8137b1c27d846fdce3c885c5ef8c3ab96a8073dbe41fcf9577bace5b2c/czsc-0.10.12-py3-none-any.whl",
    539_182,
)
RS_CZSC_WHEEL = (
    "rs_czsc-0.1.26.post260402-cp39-abi3-macosx_11_0_arm64.whl",
    "https://files.pythonhosted.org/packages/a2/f3/989b03585139a1c63559a75d3d43e8a350913f78b9c04f4c5a621f36cb7b/rs_czsc-0.1.26.post260402-cp39-abi3-macosx_11_0_arm64.whl",
    12_333_247,
)


def run(cmd: list[str], *, cwd: Path | None = None, timeout: int | None = None) -> None:
    print("+ " + " ".join(cmd))
    subprocess.run(cmd, cwd=cwd, check=True, timeout=timeout)


def fetch_wheel(name: str, url: str, expected_size: int) -> Path:
    WHEELS.mkdir(parents=True, exist_ok=True)
    path = WHEELS / name
    if path.exists() and path.stat().st_size == expected_size:
        print(f"wheel OK: {path} ({expected_size} bytes)")
        return path
    run([
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
        "1800",
        "-o",
        str(path),
        url,
    ])
    size = path.stat().st_size if path.exists() else 0
    if size != expected_size:
        raise SystemExit(f"SKIP-LOUD: partial wheel at {path} ({size}/{expected_size} bytes)")
    return path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--system-site-packages",
        action="store_true",
        help="create/use a venv that can see system pandas/pyarrow for runtime probing",
    )
    parser.add_argument(
        "--python",
        default=None,
        help="python executable used when creating the venv; defaults to python3.11, or python3 with --system-site-packages",
    )
    parser.add_argument(
        "--rs-only",
        action="store_true",
        help="probe only rs_czsc, the runtime geometry package used by differential projection",
    )
    args = parser.parse_args(argv)

    czsc = fetch_wheel(*CZSC_WHEEL)
    rs_czsc = fetch_wheel(*RS_CZSC_WHEEL)
    venv = SYSTEM_SITE_VENV if args.system_site_packages else VENV
    python_cmd = args.python or ("python3" if args.system_site_packages else "python3.11")
    if not venv.exists():
        cmd = [python_cmd, "-m", "venv"]
        if args.system_site_packages:
            cmd.append("--system-site-packages")
        cmd.append(str(venv))
        run(cmd)
    python = venv / "bin" / "python"
    run([str(python), "-m", "pip", "install", "--no-deps", "--force-reinstall", str(rs_czsc), str(czsc)])
    mods = ["rs_czsc"] if args.rs_only else ["rs_czsc", "czsc", "czsc.objects", "czsc.analyze", "czsc.enum"]
    probe = (
        "import importlib;"
        f"mods={mods!r};"
        "\nfor m in mods:\n"
        "    mod=importlib.import_module(m)\n"
        "    print(m, 'OK', getattr(mod, '__file__', None))\n"
        "    print('  attrs', [x for x in ['RawBar','NewBar','CZSC','FX','BI','ZS','Freq','Mark','Direction'] if hasattr(mod,x)])\n"
    )
    try:
        run([str(python), "-c", probe])
    except subprocess.CalledProcessError as exc:
        print(
            "SKIP-LOUD: czsc PyPI wheels installed, but runtime import failed. "
            "Install only the import-time runtime deps in the venv, then rerun: "
            f"{python} -m pip install pandas pyarrow",
            file=sys.stderr,
        )
        return exc.returncode
    print(f"czsc PyPI profile venv ready: {venv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
