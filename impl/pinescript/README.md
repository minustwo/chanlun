# Chanlun — PineScript v5 backend (documented port)

A PineScript v5 indicator that plots the Chanlun decomposition (normalize → fractal →
stroke → zhongshu → trend type) on real TradingView K-lines. The Pine source ports the
same algorithm used by the `conformance/chanlun-v1/reference_backend/` Python reference,
adapted to PineScript's bar-by-bar streaming evaluation model.

> **Important**: this is a DOCUMENTED PORT, not a conformance-verified backend.
> TradingView/PineScript cannot read the `chanlun-v1` fixture corpus at runtime or
> compare SHA-256 in CI. The honesty discipline is per stage: same algorithm as the
> reference, with explicit NAMED-OPEN residues for every divergence and every
> verification gap. See `PINESCRIPT_PORT.md` for the full mapping and the residue list.

## Files

| file | purpose |
|---|---|
| `chanlun_indicator.pine` | The PineScript v5 indicator. Load this into TradingView. |
| `PINESCRIPT_PORT.md` | Per-stage mapping commentary, confirmation-lag conventions, and the 13 NAMED-OPEN residues. **Read this first.** |
| `README.md` | This file (English). |
| `README.zh.md` | The Chinese version. |

## How to use

1. Open TradingView, pick any symbol/timeframe.
2. Open the Pine Editor (bottom of the chart). Paste the contents of
   `chanlun_indicator.pine` into a new script.
3. Click `Save` then `Add to chart`.
4. Adjust the inputs:
   - `δmin` (default 4): stroke separation threshold. See
     `PINESCRIPT_PORT.md §"stroke — Definition 4 + Lemma 2"` for the units divergence
     residue `[chanlun_v1_pinescript_stroke_dmin_units_OPEN]`.
   - `Zhongshu zone gate` (`first3` or `all`): the center-zone choice — see
     `[chanlun_zhongshu_zone_gate_OPEN]` in the parent README.
   - `Use barstate.isconfirmed` (default `true`): keep on for non-repainting behavior.
5. The chart will show:
   - Tiny blue dots at each normalized bar's H/L.
   - `T` (red) and `B` (green) labels at each fractal middle bar.
   - Lime (up) and fuchsia (down) lines for each stroke.
   - Yellow translucent boxes for each zhongshu zone (`[ZD, ZG]`).
   - A label in the top-right summarizing the running trend type + counts.

## Lineage

```
chanlun.md / chanlun.zh.md                                          (theory)
        |
        v
lean/Chanlun/*.lean                                                 (kernel proofs)
        |
        v
conformance/chanlun-v1/reference_backend/*.py                       (Python reference, batch)
        |
        v
impl/pinescript/chanlun_indicator.pine                              (THIS — Pine v5, bar-by-bar)
```

## Why no CI verification

PineScript v5 has no public headless runner, cannot read fixture files at runtime, and
cannot serialize structured output for SHA-256 comparison. The honesty residue
`[chanlun_v1_pinescript_conformance_OPEN]` covers this gap. The repo CI runs a
DISCIPLINE check (`conformance-pinescript-lint`) that verifies the absence of common
anti-patterns and the presence of the named residues — but it is NOT a true
conformance gate.

For a true SHA-equality CI gate, an offline Python/Node harness mirroring the Pine
bar-by-bar logic over the corpus would be needed. That harness is NAMED open as
`[chanlun_v1_pinescript_ci_offline_harness_OPEN]` and is out of scope for this PR.

## Honest scope

13 NAMED-OPEN residues. See `PINESCRIPT_PORT.md §"Named-open residues"` for the full
list. Highlights:

- The algorithm itself, per stage, is the same algorithm as the reference. The
  documentation port is faithful in LOGIC.
- The δmin gap is measured in CHART-BAR units, not normalized-bar units. NAMED:
  `[chanlun_v1_pinescript_stroke_dmin_units_OPEN]`.
- Walk boundaries are not available, so `trend_type` is a rolling-2-center
  approximation. NAMED: `[chanlun_v1_pinescript_trend_type_walk_boundary_OPEN]`.
- Sliding-3 zhongshu detection in streaming form may differ from batch on edge cases.
  NAMED: `[chanlun_v1_pinescript_zhongshu_sliding_3_OPEN]`.

These are not silent gaps. Each is named so the next pass knows exactly what to
discharge.

## License

Same as the parent repo (MIT, unless `LICENSE` says otherwise).
