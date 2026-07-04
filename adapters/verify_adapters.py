"""Smoke verifier for adapter boundaries."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from adapters.canonical_bars import (  # noqa: E402
    ADAPTER_INEXACT_PRICE_SCALE,
    ADAPTER_MALFORMED_BAR,
    AdapterResidue,
    ohlcv_sequence_to_integer_bars,
    rows_to_integer_bars,
)


def _must_refuse(fn, residue: str) -> None:
    try:
        fn()
    except AdapterResidue as exc:
        assert str(exc).startswith(residue), f"expected {residue}, got {exc}"
        return
    raise AssertionError(f"expected refusal {residue}")


def main() -> int:
    bars = rows_to_integer_bars(
        [{"high": "10.25", "low": "9.75"}, {"high": 11, "low": "10.00"}],
        price_scale=100,
    )
    assert bars == [{"l": 975, "h": 1025}, {"l": 1000, "h": 1100}], bars

    ohlcv = ohlcv_sequence_to_integer_bars(
        [[1700000000000, "10.00", "10.50", "9.50", "10.25", "100"]],
        price_scale=100,
    )
    assert ohlcv == [{"l": 950, "h": 1050}], ohlcv

    _must_refuse(
        lambda: rows_to_integer_bars([{"high": "10.005", "low": "9.00"}], price_scale=100),
        ADAPTER_INEXACT_PRICE_SCALE,
    )
    _must_refuse(
        lambda: rows_to_integer_bars([{"high": "8", "low": "9"}], price_scale=1),
        ADAPTER_MALFORMED_BAR,
    )
    _must_refuse(
        lambda: ohlcv_sequence_to_integer_bars([[1, "10", "11"]], price_scale=1),
        ADAPTER_MALFORMED_BAR,
    )

    print("adapters OK: exact scaling accepted; inexact scale and malformed bars refuse loud")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

