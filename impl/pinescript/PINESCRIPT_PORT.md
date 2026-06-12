# PineScript v5 port of chanlun-v1 — design notes and limitations

> **The headline**: this is a documentation port, not a
> conformance-verified backend. TradingView/PineScript cannot read the
> `conformance/chanlun-v1/fixtures/*.json` corpus at runtime, cannot
> produce structured JSON output for SHA comparison, and runs only
> inside TradingView (not in GitHub Actions). The Pine source here ports
> the same algorithm the Python reference uses, adapted to Pine's
> bar-by-bar streaming model. Every place this port diverges from the
> reference, or where Pine's evaluation model cannot match the batch
> reference, is documented below with a stable name so each item can
> be tracked in follow-up work.

## What this is

`impl/pinescript/chanlun_indicator.pine` is a PineScript v5
`indicator(...)` script that plots Chanlun 分型 (fractals), 笔 (strokes),
and 中枢 (zhongshu zones) on real TradingView candlestick (K-line) data.
The user loads the script into TradingView, attaches it to any
symbol/timeframe, and the script computes the decomposition bar-by-bar as
new candles arrive.

The algorithms it implements are:

| Stage | Reference (Python, batch) | Pine v5 port (bar-by-bar) |
|---|---|---|
| `normalize` | `reference_backend/normalize.py :: normalize_N` | streaming containment merge with `var` state across bars |
| `fractal` | `reference_backend/fractal.py :: extract_fractals` | 3-bar window classify, confirmed at right-bar's close |
| `stroke` | `reference_backend/strokes.py :: strokes` | leftmost-greedy with persistent anchor `var` |
| `zhongshu` | `reference_backend/zhongshu.py :: zhongshu` | sliding-3 ring + live-zone state machine, two zone gates |
| `trend_type` | `reference_backend/trend_type.py :: classify` | rolling classification of most-recent closed centers |
| `pipeline` | `reference_backend/pipeline.py :: run_full` | composed in-script (no separate module) |

## Why this is a documentation port (and what would change that)

PineScript v5 has hard architectural constraints that make true
`chanlun-v1` SHA-equality conformance impossible without an out-of-band
harness:

1. **No file I/O at runtime**: a Pine script cannot open
   `fixtures/*.json` or `manifest.json` to read inputs and compare
   expected outputs. Inputs are always the live candlestick stream.
2. **No JSON output**: Pine cannot serialize its internal state to a
   canonical JSON buffer that we could SHA-256 and compare against
   `expected_sha256`. The outputs are chart drawings (`line.new`,
   `box.new`, `label.new`) and `plot()` calls.
3. **No headless execution in CI**: TradingView's Pine runtime is
   closed-source and only runs inside TradingView itself. There is no
   public `pine-cli` we can invoke from a GitHub Actions runner.
4. **Bar-by-bar evaluation model**: each call sees one new bar plus
   history through `[1]`, `[2]`, etc. — it cannot do "look at the whole
   sequence then decide". This forces confirmation lags (see below).
   The reference, by contrast, is batch.

What would change the documentation-only status: an offline harness
(Python/Node) that mirrors the Pine bar-by-bar logic over the corpus
inputs. We note one as future work; if built, the implementor must keep
it byte-equivalent to the Pine source, which is itself a maintenance
burden. We have not built it here — hence the open item
`[chanlun_v1_pinescript_ci_offline_harness_OPEN]` below.

## Per-stage mapping (Python reference → Pine bar-by-bar)

### normalize — Algorithm N (Appendix A)

Reference pseudocode:

```
stack, up = [], True
for it in xs:
    if not stack: stack.append(it); continue
    top = stack[-1]
    if contained(top, it):
        stack[-1] = merge(top, it, up)
    else:
        stack.append(it)
        up = it.h > top.h
return stack
```

Pine adaptation: each new bar (`high`, `low`) is one iteration of the
Python loop. State persists in `var float n_top_l, n_top_h`; `var int
n_top_bar`; `var bool n_up`. The "committed" prior normalized bars are
kept in `n_prev_l/h/bar` and `n_prev2_l/h/bar` slots (sliding window of
3, which is exactly what the fractal stage needs).

**Confirmation lag**: zero. As soon as a non-contained bar arrives, the
prior top is committed, and the value matches what `normalize_N` would
have committed at the same position in batch mode.

**Divergence from reference**: none. The algorithm is identical; only
the state representation differs (in-place sliding window vs an
explicit `stack` list).

### fractal — Definition 3

Reference: a fractal is detected by classifying every length-3 window
`(bars[i-1], bars[i], bars[i+1])` of the normalized bars. Top iff
`H_i > both H_{i-1}, H_{i+1}` AND `L_i > both L_{i-1}, L_{i+1}`.
Bottom is the symmetric condition.

Pine adaptation: we can only classify the middle bar of a 3-bar
normalized window when the right bar of that window is known. So when a
new normalized bar `n_top` is committed (`n_just_committed == true`),
the window `(n_prev2, n_prev, n_top)` is now complete, and we classify
`n_prev`.

**Confirmation lag**: 1 normalized bar (= however many chart bars
elapsed between the middle bar's commit and the next non-contained
bar's commit). On most timeframes this is just the next chart bar.

**Divergence from reference**: none in classification logic. It only
lags the emit by one normalized bar — which is unavoidable for any
streaming Def-3 reader. Reading `[1]` and `[2]` in Pine cannot give us
"the bar that hasn't arrived yet".

### stroke — Definition 4 + Lemma 2

Reference pseudocode (`strokes.py`):

```
anchor = None
for f in fractals:
    if anchor is None:
        anchor = f; disp.append("first")
    elif f.kind == anchor.kind:
        anchor = pick_rep(anchor, f); disp.append("absorbed")   # extremal
    elif f.idx - anchor.idx >= dmin:
        emit (anchor -> f) ; anchor = f; disp.append("emit")
    else:
        disp.append("residue")
```

Pine adaptation: each new fractal (detected via `n_fractals_seen`
increment) triggers one step of the greedy. Anchor lives in `var int
anchor_idx, var string anchor_kind, var float anchor_h, anchor_l`.

**Confirmation lag**: 1 fractal (which is itself 1 normalized bar). A
stroke is confirmed at the chart bar where the right-side of the
opposite-kind fractal closes.

**Divergence from reference**: one explicit gap, tracked as
`[chanlun_v1_pinescript_stroke_dmin_units_OPEN]`:

- In the reference, `f.idx` is the index in the normalized bar list
  (post-Algorithm-N). In the Pine port, we store the chart-bar index
  where the middle bar of each fractal sat. These differ when
  normalization absorbed bars. To restore reference parity, we would
  need to maintain a separate normalized-bar counter that increments on
  every commit and use it for the gap. This is a one-day refactor; the
  divergence is documented so it is not silent. **Current effect**: the
  default δmin=4 evaluates against chart-bar gaps, so on highly-merging
  series the Pine port may emit fewer strokes than the reference (a
  non-conformant but conservative divergence).

The "too-close opposite" residue is also tracked, named
`[chanlun_v1_pinescript_stroke_close_drop_OPEN]` — the Pine port
disposes identically to the reference (no emit, no re-anchor), but the
behaviour itself is one of the open questions in the master text.

The leftmost-greedy + Lemma-2 "first admissible opposite-kind" logic is
otherwise faithful: `pick_rep` (same-kind extremal) and the
opposite-kind-and-far emit rule mirror the reference exactly.

### zhongshu — Definition (lessons 17/20)

Reference pseudocode (`zhongshu.py`):

```
while i + 2 < n:
    ZD = max(els[i..i+2].lo); ZG = min(els[i..i+2].hi)
    if ZD <= ZG:
        members = [i, i+1, i+2]; zd, zg = ZD, ZG; j = i+3
        while j < n and els[j].lo <= zg and els[j].hi >= zd:
            members.append(j)
            if zone == "all": zd = max(zd, els[j].lo); zg = min(zg, els[j].hi)
            j += 1
        emit center; i = j
    else:
        i += 1
```

Pine adaptation: each new stroke is one element. We maintain a sliding
3-ring of the last 3 elements + a "live center" state machine `var bool
zs_active`. When `zs_active == false` and 3 elements have been seen, we
test the 3-overlap; if it holds, a center forms. While `zs_active ==
true`, each new element tests overlap against the live zone; if it
overlaps, the center extends; if not, the center closes and we go back
to sliding-3 mode.

Both zone gates are supported (`first3` freezes the core `ZD`/`ZG`;
`all` re-tightens the live zone on each extension). This gate
non-uniqueness is shared with the upstream reference and is tracked as
`[chanlun_v1_pinescript_zhongshu_zone_gate_OPEN]`.

**Confirmation lag**: 1 stroke (a center forms when its 3rd member is
confirmed, and closes when the next non-overlapping stroke is
confirmed). Visually, the box on the chart extends in real time as long
as the center stays live.

**Divergence from reference**: one nuance, tracked as
`[chanlun_v1_pinescript_zhongshu_sliding_3_OPEN]`:

- The reference scans `i = 0, 1, 2, ...` and on each non-forming index,
  just slides by 1 (`i += 1`). The Pine port, in streaming form, also
  slides by 1 (each new element shifts the 3-ring). They should agree —
  but on a long history where centers are rare and the sliding window
  could "skip" a forming triple if it gets shifted out before all 3
  arrive in sequence, the Pine port's discrete shift could be
  off-by-one. We have not exhibited a counterexample; the item is
  explicitly open to be falsified or discharged.

### trend_type — lesson 17

Reference: takes a list of centers, returns one of `consolidation` /
`trend_up` / `trend_down` / `mixed` / `none`. Crisp.

Pine adaptation: there is no notion of "completed 走势" inside a Pine
indicator (a 走势 is itself a higher-level decomposition). So the Pine
port keeps a small ring of the most-recently-closed centers and reports
a rolling "last-two-step-direction" trend label.

**Confirmation lag**: 1 closed center.

**Divergence from reference**:
`[chanlun_v1_pinescript_trend_type_walk_boundary_OPEN]` — walk
boundaries are not available inside Pine without a higher-level
decomposition pass, so the running trend label is computed over the
most-recent two closed centers, not over a "completed 走势 unit". For
the reference, the input is the centers of one walk; for Pine, we
approximate.

### pipeline — end-to-end

The reference `run_full` chains all five stages. The Pine port has no
separate "pipeline" stage — by construction, each stage feeds the next
via `var` state. The end-to-end output is the chart drawing + the
running trend label. Tracked as
`[chanlun_v1_pinescript_pipeline_OPEN]`.

## Repaint discipline

PineScript repaints if you read the current-bar (`[0]`) values from an
un-confirmed bar. The script offers a user input
`i_only_confirmed = input.bool(true, ...)` that gates all state updates
behind `barstate.isconfirmed`. With this enabled (the default), the
script does not repaint: every detected fractal, stroke, and center is
determined by already-closed bars and stays put once drawn.

If you set `i_only_confirmed = false`, the script will update on the
live (still-open) bar — useful for real-time signal visualization but
the most recent fractal/stroke/center can change/disappear when the
live bar closes. This intra-bar mode is tracked as
`[chanlun_v1_pinescript_repaint_intrabar_OPEN]`: should converge to the
same final state after bar close, but this is not asserted.

**Recommended**: leave `i_only_confirmed = true` for analysis.

## Confirmation lags summary

| Stage | Lag (in stage's natural units) | Wall-clock translation |
|---|---|---|
| `normalize` | 0 | A bar's normalized form is final the next time a non-contained bar arrives. |
| `fractal` | 1 normalized bar | A fractal at middle bar M is detected when the right bar arrives. |
| `stroke` | 1 fractal | A stroke emits when the opposite-kind-and-far fractal is confirmed. |
| `zhongshu` (form) | 1 stroke | A center forms when its 3rd-element stroke is confirmed. |
| `zhongshu` (close) | 1 stroke | A center closes when the first non-overlapping stroke arrives. |
| `trend_type` | 1 closed center | The label updates each time a center closes. |

## How to verify manually

> "Verify" here means: load the indicator in TradingView and compare its
> on-chart markers against a fixture's expected output, where the
> fixture's input is replayed out-of-band. This is not a SHA-equality
> conformance check — that gap is tracked as
> `[chanlun_v1_pinescript_conformance_OPEN]`.

1. **Get a fixture and replay its bars**: pick a fixture (e.g.
   `conformance/chanlun-v1/fixtures/pipeline.synth_walk_seed3001_n40.json`).
   Its `input` field is `{ bars: [...], dmin: 4 }` where each `bar` is
   `{l, h}`. TradingView does not accept raw `{l, h}` bar uploads; the
   easiest way to replay this is to construct a CSV with synthetic
   `(time, open, high, low, close)` where `low = bar.l, high = bar.h`,
   `open = close = (l+h)/2`, time = synthetic 1-minute steps. Upload
   the CSV via the `Custom Data` / `Seed_Custom_Source` mechanism,
   then attach this indicator.
2. **Compare**: the `expected` output for the pipeline stage lists
   `normalized_bars / fractals / strokes / stroke_elements /
   zhongshu_centers / trend_type`. Visually compare:
   - The blue dots (normalized top/bottom of each committed normalized
     bar) against `expected.normalized_bars`.
   - The T/B labels at the middle-bar position of each fractal against
     `expected.fractals[i].idx`.
   - The colored stroke lines (lime = up, fuchsia = down) against
     `expected.strokes`.
   - The yellow translucent box(es) against `expected.zhongshu_centers`.
   - The top-right "trend: X" label against `expected.trend_type`.
3. **Conformant on this fixture iff**: every marker matches. Note that
   the chart-bar indices in Pine will be the replay chart-bar indices,
   while the fixture's `idx` is the post-normalize bar index — see the
   item `[chanlun_v1_pinescript_stroke_dmin_units_OPEN]`.

This is a manual, eyeball-grade verification. The verification gap is
tracked as `[chanlun_v1_pinescript_conformance_OPEN]`.

## Known limitations

Each gap is documented with a stable name so the next pass can track
exactly what to address.

| Name | What it covers | Why it's open |
|---|---|---|
| `[chanlun_v1_pinescript_normalize_OPEN]` | Algorithm-N streaming exactly matches `normalize_N` | The algorithm is identical, but we have not byte-verified the stream output against the corpus — out-of-band harness needed. |
| `[chanlun_v1_pinescript_fractal_OPEN]` | Def-3 streaming exactly matches `extract_fractals` | Same: identical logic, unverified at byte level due to no harness. |
| `[chanlun_v1_pinescript_stroke_OPEN]` | Def-4 + Lemma-2 streaming exactly matches `strokes` | Same plus the sub-items below. |
| `[chanlun_v1_pinescript_stroke_dmin_units_OPEN]` | δmin gap in chart-bar vs normalized-bar units | Pine port uses chart-bar gap; reference uses normalized-bar gap. Refactor needed: maintain a normalized-bar counter and use it for the `f.idx - anchor.idx` test. |
| `[chanlun_v1_pinescript_stroke_close_drop_OPEN]` | The "too-close opposite" residue (also tracked in the reference) | The Pine port disposes identically (no emit, no re-anchor). |
| `[chanlun_v1_pinescript_zhongshu_OPEN]` | Center decomposition streaming exactly matches `zhongshu` | Same: identical logic, unverified at byte level. |
| `[chanlun_v1_pinescript_zhongshu_sliding_3_OPEN]` | Off-by-one possibility in the sliding-3 streaming | The reference's `i += 1` scan vs the Pine's element-shift could differ on edge cases — not exhibited but not ruled out. |
| `[chanlun_v1_pinescript_zhongshu_zone_gate_OPEN]` | first3 vs all zone gate | Mirrors the upstream gate non-uniqueness; both supported, both gated by user input. |
| `[chanlun_v1_pinescript_trend_type_OPEN]` | classify exactly matches `classify` | Same: identical logic, unverified at byte level. |
| `[chanlun_v1_pinescript_trend_type_walk_boundary_OPEN]` | Walk boundary unavailable | Pine has no notion of "completed 走势" — uses a rolling 2-center window approximation. |
| `[chanlun_v1_pinescript_pipeline_OPEN]` | End-to-end composition | Composition is implicit (var-state pipe); not verified end-to-end against any pipeline fixture. |
| `[chanlun_v1_pinescript_conformance_OPEN]` | The 48-fixture SHA-equality check | Not runnable: Pine cannot read fixtures or compare SHA-256. Discharged only by an offline harness (see next). |
| `[chanlun_v1_pinescript_ci_offline_harness_OPEN]` | An offline Python/Node harness mirroring the Pine logic | Not built here. Would enable a real CI gate. |
| `[chanlun_v1_pinescript_repaint_intrabar_OPEN]` | Behavior with `i_only_confirmed = false` | The script can update on the live bar; this mode is exposed but not verified to converge to the same final state after bar close (it should, by construction, but is not asserted). |

14 named items in this port. None silent.

## CI workflow

We add a `conformance-pinescript-lint` job to
`.github/workflows/chanlun-gate.yml`. It is not a conformance gate; it
is a discipline check. The job:

1. Greps the `.pine` source for known anti-patterns:
   - `request.security` with `lookahead = barmerge.lookahead_on`
     (look-ahead bias).
   - Bare `[0]` on the live bar without `barstate.isconfirmed` guard.
2. Verifies `PINESCRIPT_PORT.md` exists and contains the documented
   limitations listed above.

Pine source compilation cannot be tested in CI (no `pine-cli`). The
item `[chanlun_v1_pinescript_ci_offline_harness_OPEN]` covers that gap.

## Stage coverage matrix

| Stage | CI-validated? | How |
|---|---|---|
| `normalize` | Documentation-only | Same algorithm as reference; no byte test. |
| `fractal` | Documentation-only | Same. |
| `stroke` | Documentation-only | Same, plus the `[chanlun_v1_pinescript_stroke_dmin_units_OPEN]` known divergence. |
| `zhongshu` | Documentation-only | Same. |
| `trend_type` | Documentation-only | Same, plus the `[chanlun_v1_pinescript_trend_type_walk_boundary_OPEN]` known divergence. |
| `pipeline` | Documentation-only | Composition is implicit. |
| `(linting)` | CI-validated | `conformance-pinescript-lint` job verifies discipline (anti-patterns absent, items documented). |

**Summary**: 0 of 6 stages are CI-validated in the SHA-equality sense;
6 of 6 are documentation-ported with documented limitations for the
verification gap. Lint discipline is CI-validated.

## Provenance

```
chanlun.md / chanlun.zh.md                                         (Lessons 3-5, 17, 20, App-A)
        |
        v
lean/Chanlun/*.lean                                                (kernel-verified theorems)
        |
        v
conformance/chanlun-v1/reference_backend/*.py                      (pure-stdlib Python, batch)
        |
        v
impl/pinescript/chanlun_indicator.pine                             (Pine v5, bar-by-bar)
        |
        v
TradingView chart                                                  (visual decomposition on live K-lines)
```

## License

Same as the parent repo (MIT, unless `LICENSE` says otherwise).
