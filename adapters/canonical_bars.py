"""Adapters into the canonical `chanlun-v1` bar wire shape.

The proven core consumes integer bars: `{"l": int, "h": int}`. Market feeds and
external libraries often carry decimal strings or floats. This adapter requires
an explicit integer `price_scale` and refuses inexact conversion instead of
rounding silently.
"""
from __future__ import annotations

from decimal import Decimal, InvalidOperation
from typing import Iterable, Mapping, Sequence


ADAPTER_INEXACT_PRICE_SCALE = "[adapter_inexact_price_scale]"
ADAPTER_MALFORMED_BAR = "[adapter_malformed_bar]"


class AdapterResidue(ValueError):
    """Named adapter refusal. The message starts with a catalog-style residue."""


def _decimal(value) -> Decimal:
    try:
        return Decimal(str(value))
    except (InvalidOperation, ValueError) as exc:
        raise AdapterResidue(f"{ADAPTER_MALFORMED_BAR} price is not decimal: {value!r}") from exc


def _scaled_int(value, price_scale: int) -> int:
    scaled = _decimal(value) * Decimal(price_scale)
    if scaled != scaled.to_integral_value():
        raise AdapterResidue(
            f"{ADAPTER_INEXACT_PRICE_SCALE} value {value!r} is not exact at scale {price_scale}"
        )
    return int(scaled)


def rows_to_integer_bars(
    rows: Iterable[Mapping],
    *,
    high_key: str = "high",
    low_key: str = "low",
    price_scale: int,
) -> list[dict]:
    """Convert high/low rows to canonical integer bars.

    `price_scale=100` means input prices with cents precision become integer
    cents. A row whose low exceeds high is malformed and refused.
    """
    if not isinstance(price_scale, int) or price_scale <= 0:
        raise AdapterResidue(f"{ADAPTER_MALFORMED_BAR} price_scale must be a positive integer")

    out = []
    for i, row in enumerate(rows):
        if high_key not in row or low_key not in row:
            raise AdapterResidue(f"{ADAPTER_MALFORMED_BAR} row {i} missing {high_key!r}/{low_key!r}")
        h = _scaled_int(row[high_key], price_scale)
        l = _scaled_int(row[low_key], price_scale)
        if l > h:
            raise AdapterResidue(f"{ADAPTER_MALFORMED_BAR} row {i} has low > high after scaling")
        out.append({"l": l, "h": h})
    return out


def ohlcv_sequence_to_integer_bars(rows: Sequence[Sequence], *, price_scale: int) -> list[dict]:
    """Convert common OHLCV rows `[ts, open, high, low, close, volume, ...]`.

    Only high and low are projected into canonical geometry. Time, open, close,
    and volume stay product-layer data.
    """
    projected = []
    for i, row in enumerate(rows):
        if len(row) < 4:
            raise AdapterResidue(f"{ADAPTER_MALFORMED_BAR} OHLCV row {i} has fewer than 4 fields")
        projected.append({"high": row[2], "low": row[3]})
    return rows_to_integer_bars(projected, price_scale=price_scale)


__all__ = [
    "ADAPTER_INEXACT_PRICE_SCALE",
    "ADAPTER_MALFORMED_BAR",
    "AdapterResidue",
    "ohlcv_sequence_to_integer_bars",
    "rows_to_integer_bars",
]

