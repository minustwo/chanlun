"""Fetch minimal optional external source trees for runtime differentials.

The fetched files live outside the repository under `/tmp/chanlun-externals`.
They are evidence inputs for `differential/compare.py`, not vendored code.
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys
import urllib.parse
import urllib.request
from pathlib import Path


OUT = Path("/tmp/chanlun-externals")


def fetch_chanpy() -> None:
    repo = "Vespa314/chan.py"
    root = OUT / "chan.py"
    tmp = OUT / "chan.py.tmp"
    if tmp.exists():
        shutil.rmtree(tmp)
    tmp.mkdir(parents=True)

    api = f"https://api.github.com/repos/{repo}/git/trees/main?recursive=1"
    with urllib.request.urlopen(api, timeout=30) as resp:
        tree = json.load(resp)["tree"]

    prefixes = (
        "Bi/",
        "BuySellPoint/",
        "ChanModel/",
        "Combiner/",
        "Common/",
        "DataAPI/",
        "KLine/",
        "Math/",
        "Seg/",
        "ZS/",
    )
    paths = []
    for item in tree:
        path = item["path"]
        if item.get("type") != "blob" or not path.endswith(".py"):
            continue
        if "/" not in path or path.startswith(prefixes):
            paths.append(path)

    base = f"https://raw.githubusercontent.com/{repo}/main/"
    for path in paths:
        target = tmp / path
        target.parent.mkdir(parents=True, exist_ok=True)
        url = base + urllib.parse.quote(path)
        with urllib.request.urlopen(url, timeout=30) as resp:
            target.write_bytes(resp.read())

    if root.exists():
        shutil.rmtree(root)
    tmp.rename(root)
    print(f"fetched chan.py minimal runtime tree: {len(paths)} files -> {root}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", choices=["chanpy"], help="external source to fetch")
    args = parser.parse_args(argv)
    if args.source == "chanpy":
        fetch_chanpy()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
