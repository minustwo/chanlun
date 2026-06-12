# Chanlun — PineScript v5 backend (documentation port)

A PineScript v5 indicator that plots the Chanlun decomposition
(normalize → fractal → stroke → zhongshu → trend type) on real
TradingView K-lines. The Pine source ports the same algorithm used by
the `conformance/chanlun-v1/reference_backend/` Python reference,
adapted to PineScript's bar-by-bar streaming evaluation model.

> **Important**: this is a documentation port, not a
> conformance-verified backend. TradingView/PineScript cannot read the
> `chanlun-v1` fixture corpus at runtime or compare SHA-256 in CI. Each
> divergence and verification gap is named explicitly. See
> `PINESCRIPT_PORT.md` for the full per-stage mapping and the list of
> known limitations.

## Files

| file | purpose |
|---|---|
| `chanlun_indicator.pine` | The PineScript v5 indicator. Load this into TradingView. |
| `PINESCRIPT_PORT.md` | Per-stage mapping commentary, confirmation-lag conventions, and the 13 known limitations. **Read this first.** |
| `README.md` | This file (English). |
| `README.zh.md` | The Chinese version. |

## How to use

1. Open TradingView, pick any symbol/timeframe.
2. Open the Pine Editor (bottom of the chart). Paste the contents of
   `chanlun_indicator.pine` into a new script.
3. Click `Save` then `Add to chart`.
4. Adjust the inputs:
   - `δmin` (default 4): stroke separation threshold. The unit
     discrepancy between chart-bar and normalized-bar gaps is documented
     in `PINESCRIPT_PORT.md §"stroke — Definition 4 + Lemma 2"`.
   - `Zhongshu zone gate` (`first3` or `all`): the center-zone choice;
     both readings are supported here (parent README explains the
     non-uniqueness).
   - `Use barstate.isconfirmed` (default `true`): keep on for
     non-repainting behaviour.
5. The chart will show:
   - Tiny blue dots at each normalized bar's H/L.
   - `T` (red) and `B` (green) labels at each fractal middle bar.
   - Lime (up) and fuchsia (down) lines for each stroke.
   - Yellow translucent boxes for each zhongshu zone (`[ZD, ZG]`).
   - A label in the top-right summarizing the running trend type +
     counts.

## Provenance

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
impl/pinescript/chanlun_indicator.pine                              (Pine v5, bar-by-bar)
```

## Why no CI verification

PineScript v5 has no public headless runner, cannot read fixture files
at runtime, and cannot serialize structured output for SHA-256
comparison. The repo CI runs a *discipline check*
(`conformance-pinescript-lint`) that verifies the absence of common
anti-patterns and the presence of the documented limitations — but it
is not a true conformance gate.

For a true SHA-equality CI gate, an offline Python or Node harness
mirroring the Pine bar-by-bar logic over the corpus would be needed.
That harness is listed as a future-work item in `PINESCRIPT_PORT.md`
and is out of scope here.

## Scope and limitations

13 known limitations. See `PINESCRIPT_PORT.md §"Known limitations"` for
the full list. Highlights:

- The algorithm itself, per stage, is the same algorithm as the
  reference. The port is faithful in *logic*.
- The δmin gap is measured in chart-bar units, not normalized-bar units.
  A future refactor would maintain a separate normalized-bar counter and
  test against that.
- Walk boundaries are not available, so `trend_type` is a
  rolling-2-center approximation.
- Sliding-3 zhongshu detection in streaming form may differ from batch
  on edge cases (no counterexample exhibited, but not ruled out).

Each one is documented so the next pass knows exactly what to address.

## License

Same as the parent repo (MIT, unless `LICENSE` says otherwise).
