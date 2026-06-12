# Chanlun — Mathematical Formalism

> The mathematical form of Chanlun. Each definition and theorem below is
> proven in `lean/Chanlun/` with no admitted lemmas (`sorry`-free). This
> document is the human-readable narrative; the Lean modules are the
> trusted artifact.
>
> Chinese version: [chanlun.zh.md](chanlun.zh.md).

---

## §0 Notation

All arithmetic is over `ℤ` (integers) with `ℕ` for indices. There is no
floating-point dependency in the formalism; prices arrive as integer
scaled values (e.g., for CME E-mini futures with a 0.25 tick size,
multiply prices by 4). This integer-only discipline keeps every theorem
decidable and the kernel proofs constructive.

* `Bar := { h : ℤ, l : ℤ }` — a candlestick: high, low.
* `Interval := { l : ℤ, h : ℤ }` — same data, alternate field order
  (used by the normalization algorithm; bridged via `toBar : Interval → Bar`).
* `Fractal := { idx : ℕ, kind : FractalKind, h : ℤ, l : ℤ }` with
  `FractalKind ∈ { top, bottom, neither }`.
* `Stroke := { from_idx : ℕ, to_idx : ℕ, dir : StrokeDir }` with
  `StrokeDir ∈ { up, down }`.
* `Center := { start : ℕ, end_ : ℕ, ZD : ℤ, ZG : ℤ }` (Zhongshu 中枢).

---

## §1 Definition 3 — Fractal (分型)

### Top fractal

A 3-bar window `(a, b, c)` is a **top fractal** iff

```
b.h > a.h  ∧  b.h > c.h  ∧  b.l > a.l  ∧  b.l > c.l.
```

### Bottom fractal

`(a, b, c)` is a **bottom fractal** iff

```
b.h < a.h  ∧  b.h < c.h  ∧  b.l < a.l  ∧  b.l < c.l.
```

### Classification

```
classifyDef3(a, b, c) := if isTopFractal then top
                        else if isBottomFractal then bottom
                        else neither
```

### Theorem 1.1 (`def3_trichotomy`)

For every 3-bar window, `classifyDef3` returns exactly one of
`{top, bottom, neither}`, and top/bottom are mutually exclusive (no
window satisfies both).

### Theorem 1.2 (`fractal_slot_equiv_def3`)

The operator-side integer-coded classifier (`0 = top`, `1 = bottom`,
`2 = neither`) equals `kindToInt ∘ classifyDef3` for every window.

Lean module: [`Chanlun.Fractal`](lean/Chanlun/Fractal.lean).

---

## §2 Algorithm N — Containment-handling (Appendix A)

### Containment

Two adjacent intervals `(a, b)` are in *containment* iff
`(b.l ≤ a.l ∧ a.h ≤ b.h) ∨ (a.l ≤ b.l ∧ b.h ≤ a.h)`.

### `noAdjContainment`

A list of intervals is `noAdjContainment` iff no adjacent pair is in
containment.

### Single-pass `normalize`

Walks the list with a directional `pushOne` step:

* same direction + new bar contained in stack-top: merge by `[max, max]`
  (up) / `[min, min]` (down);
* otherwise push.

### Theorem 2.1 (`normalize_no_adjacent_containment`)

For every input `xs`, `noAdjContainment (normalize xs).1`.

Equivalently: a single left-to-right pass with the directional merge
already produces the containment-free quotient — no second pass needed.

Lean module: [`Chanlun.Normalize`](lean/Chanlun/Normalize.lean).

---

## §3 Pipeline composition (N → Def-3)

### `isInclusionNormalized`

A 3-bar window `(a, b, c)` is *inclusion-normalized* iff neither
neighbour's interval is contained in the middle or vice versa.

### Theorem 3.1 (`pipeline_inclusion_normalized`)

```
∀ xs, ∀ a b c rest,
  (normalize xs).1 = a :: b :: c :: rest →
  isInclusionNormalized (toBar b) (toBar a) (toBar c).
```

### Theorem 3.2 (`pipeline_fractal_classification_well_defined`)

After Algorithm N, every interior 3-window in the result stack
classifies determinately to one of `{top, bottom, neither}`.

Lean module: [`Chanlun.Pipeline`](lean/Chanlun/Pipeline.lean).

---

## §4 Definition 4 — Stroke (笔)

### Construction (leftmost-greedy)

A walk over the fractal list with one alternating *anchor*:

* no anchor yet → set anchor to current fractal `f`;
* same-kind fractal → keep the extremal representative (`pickRep`);
* opposite-kind, gap `≥ δmin` → **emit** stroke `(anchor → f)`, re-anchor to `f`;
* opposite-kind, gap `< δmin` → drop (see "Known limitations" in
  [`README.md`](README.md)).

### Theorem 4.1 (`stroke_emits_separated`, property B)

Every emitted stroke satisfies `δmin ≤ to_idx − from_idx`.

### Theorem 4.2 (`stroke_emits_alternate`, property A)

Consecutive strokes in the in-fold output have opposite directions.

### Theorem 4.3 (`strokes_separated`)

The user-facing reversed-order stroke list inherits the separation
property via `List.mem_reverse`.

Lean module: [`Chanlun.Stroke`](lean/Chanlun/Stroke.lean).

---

## §5 Lemma 2 (strong form) — Stroke uniqueness

### Structural validity predicate `IsValidBi`

A recursive predicate on `(Option Fractal × List Fractal × ℤ × List Stroke)`
mirroring `step`'s case analysis. Captures: *from-endpoint is the
extremal representative of its same-kind run; to-endpoint is the
leftmost opposite-kind admissible fractal*.

### Theorem 5.1 (`strokes_unique`)

```
∀ frs δmin alt, IsValidBi frs δmin alt → alt = strokes frs δmin.
```

Any structurally valid Bi decomposition equals the canonical streaming
output. The proof goes through a generalized fold-vs-alt invariant
`fold_consumes_alt` carried by induction on `frs`.

Lean module: [`Chanlun.StrokeUniqueness`](lean/Chanlun/StrokeUniqueness.lean).

---

## §6 Definitions 5–16 + Theorem 1 — Segment (线段)

### The BoundedFix recursion

`segments : (find_term : ℕ → Option ℕ) → (find_term_ge : property) → ℕ → ℕ → List Segment`.

Parameterized over a *leftmost-≥-a* oracle `find_term` and its contract
`find_term_ge : ∀ a j, find_term a = some j → a ≤ j`. The full
feature-sequence Φ + overlap admissibility internals of `find_term` are
not re-derived here (see "Known limitations" in `README.md`); the Lean
recursion only needs the contract `find_term_ge`.

### Theorem 6.1 (`segments_partition`, property P)

The emitted segments contiguously partition `[a, n)`.

### Theorem 6.2 (`segments_terminate`, property T)

At most `n - a + 1` segments are emitted (well-founded, finite list).

### Theorem 6.3 (`segment_advance_strictly_increasing`)

The central termination lemma:
`find_term a = some j → a ≤ j → n - (j + 1) < n - a`.
Strict decrease of the `n − a` measure ⇒ BoundedFix is well-founded.

Lean module: [`Chanlun.Segment`](lean/Chanlun/Segment.lean).

---

## §7 Zhongshu (中枢, lesson 17/20)

### Construction

For a sequence of elements `[lo, hi]` indexed by ℕ:

* scan `i` from `0`;
* if `els.length ≤ i + 2` → stop;
* let `ZD := max(els[i].lo, els[i+1].lo, els[i+2].lo)` and
  `ZG := min(els[i].hi, els[i+1].hi, els[i+2].hi)`;
* if `ZD ≤ ZG` (genuine overlap) → emit `⟨i, extendEnd(i+3), ZD, ZG⟩`
  and continue at `extendEnd + 1`;
* else → slide `i := i + 1`.

The extension function `extendEnd els g zd zg j` walks `j` forward while
`els[j]` overlaps the live zone. Parameter `g : ZoneGate ∈ {first3, all_}`
controls re-tightening:

* `first3` keeps `(zd, zg)` fixed;
* `all_` tightens to `(max zd els[j].lo, min zg els[j].hi)`.

The master text leaves this choice underspecified; we provide both
readings and prove both are valid (see "Known limitations" in
`README.md`).

### Theorem 7.1 (`zhongshu_valid`)

For every Center `c` produced by `zhongshu`, `c.ZD ≤ c.ZG`. By
construction via the form gate.

### Theorem 7.2 (`zhongshu_disjoint`)

Consecutive Centers `c₁ :: c₂ :: rest` satisfy `c₁.end_ < c₂.start`.

### Theorem 7.3 (`extendEnd_ge`)

`j - 1 ≤ extendEnd els g zd zg j`. The central termination lemma that
gives `zhongshu` its well-founded termination on the `els.length − i`
measure.

Lean module: [`Chanlun.Zhongshu`](lean/Chanlun/Zhongshu.lean).

---

## §8 TrendType (lesson 17)

### Classification

```
classify : List Center → WalkType
classify []           = none_
classify [_]          = consolidation
classify (c₁::c₂::rs) = if allUp then trend_up
                      else if allDown then trend_down
                      else mixed
```

`allUp` / `allDown` are decidable predicates on the consecutive
`stepDir` function (`up` iff next Center's `ZD > prev.ZG`; `down` iff
next's `ZG < prev.ZD`; `neither` otherwise).

### Theorem 8.1 (`classify_total`)

`classify cs` is one of `{none_, consolidation, trend_up, trend_down, mixed}`
for every `cs`. Total and never-silent.

### Theorem 8.2 (`classify_trend_monotone`)

```
(classify cs = trend_up   → allStepsAreUp cs) ∧
(classify cs = trend_down → allStepsAreDown cs).
```

The "sequentially-same-direction" qualifier is genuinely enforced.

Lean module: [`Chanlun.TrendType`](lean/Chanlun/TrendType.lean).

---

## §9 Bi reachable-domain determinism

### `noAdjBarContainment`

Bar-level lift of `noAdjContainment`. Holds on the post-`normalize`
reachable domain.

### Theorem 9.1 (`fractals_alternate_on_containment_free`)

```
∀ bars, noAdjBarContainment bars → AlternateKinds (fractalKinds bars).
```

On the reachable (containment-free) domain, the fractal kinds strictly
alternate — so the three Bi-endpoint readings (leftmost / extremal /
keep-latter) **coincide** on every reachable input. The gate-relativity
finding on arbitrary inputs (44–55% disagreement) is an artifact of
how the input domain is encoded; on the reachable domain Chanlun's
uniqueness claim is real.

Proof chain:

1. `dichotomy_of_no_containment` — any non-contained pair is strictly
   directional (`goesUp` or `goesDown`) in both `h` and `l`.
2. `neither_preserves_direction` — a `.neither` window on
   containment-free input forces `dir(b, c) = dir(a, b)`.
3. `fractalKinds_first_kind_after_{up,down}` — leading direction forces
   first emit kind.
4. Main theorem by induction.

Lean module:
[`Chanlun.BiReachableDeterminism`](lean/Chanlun/BiReachableDeterminism.lean).

---

## §10 LevelRecursion (lesson 24) — "Every trend must complete"

### `centerSize`

```
centerSize c := c.end_ + 1 − c.start.
```

### Theorem 10.1 (`centerSize_ge_3`)

Every Center emitted by `zhongshu` satisfies `centerSize c ≥ 3`. Direct
consequence of `extendEnd_ge` (Theorem 7.3): the extension starts at
`i + 3` and never returns earlier than `i + 2`, so `end_ ≥ start + 2`
and `size ≥ 3`.

### Theorem 10.2 (`lift_strict_drop`)

```
∀ els g, zhongshu els g 0 ≠ [] →
  (zhongshu els g 0).length + 2 ≤ ((zhongshu els g 0).map centerSize).sum.
```

If any Zhongshu forms, the next-level element count drops by at least 2.
Combined with `ℕ`-well-foundedness on `els.length`, the level recursion
terminates in ≤ `n / 2` levels — the formal content of "every trend must
complete" (lesson 24).

Lean module:
[`Chanlun.LevelRecursion`](lean/Chanlun/LevelRecursion.lean).

---

## §11 WalkDecomposition (lesson 17)

### `decompose : List Center → List Walk`

Walks the Center sequence emitting the **maximal** Walk at each step:

* `consolidation` if a single Center remains;
* `trend_up` for the maximal up-stepping run;
* `trend_down` for the maximal down-stepping run.

Boundary rule: a new Walk starts the moment adding the next Center
would change the WalkType (or break the same-direction invariant).

### Theorem 11.1 (`decompose_partition`)

```
Σ (walks.map walkSize) = centers.length.
```

Every Center index belongs to exactly one Walk.

### Theorem 11.2 (`decompose_monotonic`)

Walk boundaries are strictly increasing in `start`: for adjacent walks
`w₁, w₂`, `w₁.end_ + 1 = w₂.start`.

### Theorem 11.3 (`decompose_type_homogeneous`)

Each emitted Walk has a homogeneous WalkType: every Center in the
Walk's span classifies under the Walk's type. The `mixed` WalkType
cannot be emitted by `decompose` (proven by the split criterion);
`mixed` only arises from a downstream merge, which is listed as a
future-work item.

Lean module:
[`Chanlun.WalkDecomposition`](lean/Chanlun/WalkDecomposition.lean).

---

## §12 Other formalized layers

Additional modules added in subsequent passes cover:

* `Chanlun.StrokesIsValidBiCorollary` (`strokes_isValidBi`,
  `strokes_iff_IsValidBi`) — non-vacuity + biconditional for
  `strokes_unique`.
* `Chanlun.BiEndpointSubResidues` — closes three sub-results connected
  to `Chanlun.StrokeUniqueness`: TO-endpoint leftmost-vs-extremal,
  drop-branch preservation, output-order alternation lift.
* `Chanlun.BiReachableDeterminismBridge` — `Interval → Bar` plumbing for
  the §9 alternation theorem.
* `Chanlun.ZhongshuExtension` — the four named transitions
  (延伸 / 扩展 / 新生 / endNoRebirth) + 9-段 upgrade trigger.
* `Chanlun.Beichi` — divergence 力度 comparison (lessons 24/27/29),
  integer-exact displacement + slope.
* `Chanlun.PanzhengBeichi` — 盘整背驰 (lesson 37) single-center A-vs-C
  classifier.
* `Chanlun.ThirdBuysell` — 第三类买卖点 (lesson 20).
* `Chanlun.FirstSecondBuysell` — 第一/第二类买卖点 (lesson 24) +
  measure-gate inheritance.
* `Chanlun.RecursiveSubBspBeichi` — recursive 三买卖 + 背驰 (lessons
  20/24/27/29 lifted to sub-levels).
* `Chanlun.IntervalNesting` — lesson 65/66 区间套 base classifier and
  the strict-descent termination measure.

---

## §13 Open questions

Limitations and open questions not yet discharged in the Lean library
are listed in [`README.md`](README.md) under
"Known limitations and open questions". Each one is surfaced rather
than hidden.

---

## §14 Attribution

The Chanlun theory itself belongs to the 缠中说禅 tradition. The
formal system written above and the Lean encoding under `lean/Chanlun/`
are this repository's contribution. The reachable-domain audit
correction (§9) and the lift-termination measure (§10) are the
non-obvious mathematical contributions of the formalization;
everything else is the published theory in Lean form.

---

## §15 License

The formalization, this document, the reference oracles, and the CI
workflow are released under MIT; see `LICENSE` if present.
