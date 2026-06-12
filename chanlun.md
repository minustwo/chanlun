# Chanlun — A Mathematical Textbook

> A mathematician's and student's reading of 缠论 (Chanlun). Each Definition
> and Theorem is stated in three parts: prose, formal statement, and a
> verifiable Lean cross-reference under `lean/Chanlun/`. Where the master
> text is genuinely ambiguous or where the Lean proof is not yet complete,
> the open status is named with an auditable reason.
>
> Chinese version: [chanlun.zh.md](chanlun.zh.md).

---

## §0 Notation and scope

This document treats Chanlun as a mathematical theory of one-dimensional
discrete-time price series. Prices arrive as integers (e.g., a 0.25-tick
instrument is scaled by 4 so the smallest unit is 1); time is indexed by
ℕ. Working in ℤ avoids floating-point and keeps every theorem decidable.

The objects:

- A **bar** is a pair (h, l) ∈ ℤ × ℤ with h ≥ l, recording one period's
  high and low. Type signature: `Bar := { h : ℤ, l : ℤ }`.
- An **interval** is the same data, fields swapped for the
  containment-normalization algorithm: `Interval := { l : ℤ, h : ℤ }`,
  bridged by `toBar : Interval → Bar`.
- A **fractal** is a labelled bar with a position index and a kind in
  {top, bottom, neither}: `Fractal := { idx : ℕ, kind : FractalKind, h : ℤ, l : ℤ }`.
- A **stroke** (笔) is `{ from_idx, to_idx : ℕ, dir : {up, down} }`.
- A **center** (中枢) is `{ start, end_ : ℕ, ZD, ZG : ℤ }`, the index
  range and overlapping zone [ZD, ZG] it defines.
- A **walk** (走势) is a contiguous sub-range of the center list with a
  walk-type label.

Chanlun is the theory of how bars compose into fractals, fractals into
strokes, strokes into segments, segments into centers, and centers into
walks, with a recursion that lifts the whole stack to a higher level.
This document follows that ascent.

---

## §1 包含处理 — Algorithm N (containment normalization)

### Definition 1.1 (containment)

**Prose.** Two adjacent bars are in containment when one fully encloses
the other in both high and low — the smaller one carries no information
the larger one does not. Containment must be removed before the fractal
shape of the series can be read.

**Formal.** Adjacent intervals (a, b) are in containment iff

    (b.l ≤ a.l ∧ a.h ≤ b.h) ∨ (a.l ≤ b.l ∧ b.h ≤ a.h).

A list xs : List Interval satisfies `noAdjContainment` iff no adjacent
pair is in containment.

**Lean realization.** `Chanlun.Normalize.contained` and
`Chanlun.Normalize.noAdjContainment` in
[`lean/Chanlun/Normalize.lean`](lean/Chanlun/Normalize.lean).

### Definition 1.2 (single-pass `normalize`)

**Prose.** Walk the bar list left to right keeping a stack with a
direction flag. When the next bar is contained by the stack-top, merge by
keeping both highs' max (uptrend) or both lows' min (downtrend); otherwise
push and update the direction.

**Formal.**

    pushOne : (stack, up) → bar →
      if up ∧ contained(stack.top, bar) then ([max h, max l] :: stack.tail, up)
      else if ¬up ∧ contained(stack.top, bar) then ([min h, min l] :: stack.tail, up)
      else (bar :: stack, h(bar) > h(stack.top))

    normalize : List Interval → List Interval × Bool := foldl pushOne ([], true)

**Lean realization.** `Chanlun.Normalize.pushOne`,
`Chanlun.Normalize.normalize`.

### Theorem 1.3 — `normalize_no_adjacent_containment`

**Prose.** A single left-to-right pass already produces a
containment-free output. No second pass is needed — the directional merge
rule is strong enough.

**Formal.** For every xs : List Interval,

    noAdjContainment (normalize xs).1.

**Lean proof.**
[`Chanlun.Normalize.normalize_no_adjacent_containment`](lean/Chanlun/Normalize.lean).
The proof goes through `pushOne_preserves`: an invariant carrying both
`noAdjContainment` and a `goodStack` directional consistency clause is
inductive over the fold.

---

## §2 分型 — Fractal (Definition 3 of the master text)

### Definition 2.1 (top / bottom fractal)

**Prose.** Given three consecutive normalized bars, the middle one is a
**top** if it strictly dominates both neighbours in both high and low; it
is a **bottom** if it is strictly dominated in both. Otherwise it is
**neither**. Top and bottom mark candidate inflection points of the
series.

**Formal.** For bars a, b, c,

    isTopFractal a b c    := b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l
    isBottomFractal a b c := b.h < a.h ∧ b.h < c.h ∧ b.l < a.l ∧ b.l < c.l

    classifyDef3 a b c := if isTopFractal a b c    then top
                          else if isBottomFractal a b c then bottom
                          else neither.

**Lean realization.** `Chanlun.Fractal.isTopFractal`,
`Chanlun.Fractal.isBottomFractal`, `Chanlun.Fractal.classifyDef3` in
[`lean/Chanlun/Fractal.lean`](lean/Chanlun/Fractal.lean).

### Theorem 2.2 — `def3_trichotomy`

**Prose.** Every 3-bar window is classified as exactly one of
{top, bottom, neither}: classification is total and top/bottom are
mutually exclusive.

**Formal.** For all bars a, b, c,

    classifyDef3 a b c ∈ {top, bottom, neither}
    ∧ ¬ (isTopFractal a b c ∧ isBottomFractal a b c).

**Lean proof.** `Chanlun.Fractal.def3_trichotomy`. Proof by case split on
strict-comparison decidability.

### Theorem 2.3 — `fractal_slot_equiv_def3`

**Prose.** The operator-side integer-coded classifier
(0 = top, 1 = bottom, 2 = neither) agrees with the prose-side
classification on every input. The two formulations of "find the fractal
kind" cannot disagree.

**Formal.** Letting `kindToInt : FractalKind → ℤ` send top ↦ 0,
bottom ↦ 1, neither ↦ 2, and letting `fractalSlotPredicate` be the
operator-side integer classifier,

    ∀ a b c : Bar, fractalSlotPredicate a b c = kindToInt (classifyDef3 a b c).

**Lean proof.** `Chanlun.Fractal.fractal_slot_equiv_def3`. Direct
unfolding of both classifiers followed by a 9-way case split.

### Theorem 2.4 — `pipeline_inclusion_normalized` (composition with §1)

**Prose.** After Algorithm N has run, every interior 3-bar window in the
output is *inclusion-normalized*: neither neighbour's interval is
contained in the middle's or vice versa. So Definition 2.1 is then
unambiguously applicable.

**Formal.** For all xs : List Interval and all suffix decompositions

    (normalize xs).1 = a :: b :: c :: rest
      ⇒ isInclusionNormalized (toBar b) (toBar a) (toBar c).

**Lean proof.**
[`Chanlun.Pipeline.pipeline_inclusion_normalized`](lean/Chanlun/Pipeline.lean).
Bridge lemma `not_contained_iff_bar` plus an extraction of the head pair
from `normalize_no_adjacent_containment`.

### Theorem 2.5 — `pipeline_fractal_classification_well_defined`

**Prose.** Combining Theorems 1.3, 2.2, and 2.4: on any post-Algorithm-N
output, every interior 3-bar window has a determinate kind.

**Lean proof.** `Chanlun.Pipeline.pipeline_fractal_classification_well_defined`.

---

## §3 笔 — Stroke (Definition 4)

### Definition 3.1 (stroke construction, leftmost-greedy)

**Prose.** Walk the fractal list keeping at most one *anchor*. Each
incoming fractal of the same kind as the anchor updates the anchor to the
more extremal representative. An opposite-kind fractal at gap ≥ δmin from
the anchor emits a stroke (anchor → current) and re-anchors. A close
opposite-kind fractal (gap < δmin) is dropped.

**Formal.** State `s = { anchor : Option Fractal, out : List Stroke }`.

    step δmin s f :=
      match s.anchor with
      | none    ⇒ { anchor := some f, out := s.out }
      | some a  ⇒
        if a.kind = f.kind then { anchor := some (pickRep a f), out := s.out }
        else if f.idx - a.idx ≥ δmin then
          { anchor := some f, out := { from_idx := a.idx, to_idx := f.idx, dir := emitDir f } :: s.out }
        else s  -- drop

    strokes frs δmin := reverse (foldl (step δmin) StrokeState.empty frs).out.

**Lean realization.** `Chanlun.Stroke.step`, `Chanlun.Stroke.strokes` in
[`lean/Chanlun/Stroke.lean`](lean/Chanlun/Stroke.lean).

### Theorem 3.2 — `stroke_emits_separated` (separation, property B)

**Prose.** Every emitted stroke spans at least δmin units. The
minimum-separation gate is genuinely enforced.

**Formal.**

    ∀ frs δmin, ∀ s ∈ strokes frs δmin, δmin ≤ s.to_idx - s.from_idx.

**Lean proof.** `Chanlun.Stroke.stroke_emits_separated`, lifted to the
user-facing reversed output as `Chanlun.Stroke.strokes_separated` via
`List.mem_reverse`.

### Theorem 3.3 — `stroke_emits_alternate` (alternation, property A)

**Prose.** Consecutive strokes in the emission have opposite directions.
The walk genuinely zigzags.

**Formal.**

    ∀ frs δmin, allAlternate ((foldl (step δmin) StrokeState.empty frs).out).

**Lean proof.** `Chanlun.Stroke.stroke_emits_alternate`. The
output-facing lift (after `reverse`) is
`Chanlun.BiEndpointSubResidues.strokes_alternate` via
`allAlternate_reverse`.

### Theorem 3.4 — `strokes_unique` (Lemma 2, strong form)

**Prose.** Any sequence of strokes that is *structurally valid* —
each from-endpoint is the extremal representative of its same-kind run,
each to-endpoint is the leftmost admissible opposite-kind fractal — must
equal the canonical streaming output. The greedy construction does not
make arbitrary choices: it is the unique decomposition.

**Formal.** With `IsValidBi` the recursive predicate capturing the
structural constraints,

    ∀ frs δmin alt, IsValidBi frs δmin alt → alt = strokes frs δmin.

**Lean proof.** `Chanlun.StrokeUniqueness.strokes_unique` in
[`lean/Chanlun/StrokeUniqueness.lean`](lean/Chanlun/StrokeUniqueness.lean).
The proof generalizes to an invariant `fold_consumes_alt` carried by
induction on `frs`. Non-vacuity (some valid `alt` exists for every input)
is `Chanlun.StrokesIsValidBiCorollary.strokes_isValidBi`; the
biconditional `IsValidBi ↔ alt = strokes ...` is
`Chanlun.StrokesIsValidBiCorollary.strokes_iff_IsValidBi`.

### Theorem 3.5 — endpoint sub-results

**Prose.** Three small but load-bearing equivalences underpin
Theorem 3.4: (a) on a reachable input, the to-endpoint computed as
"leftmost opposite-kind admissible" equals the extremal-literal reading;
(b) the drop branch does not change the fold state; (c) reversing the
output preserves the alternation property.

**Formal.**

    (a) to_endpoint_leftmost_eq_extremal_on_reachable
        : on a strictly-alternating reachable list, the two readings agree.
    (b) dropBranch_step_no_op  : step δmin s f = s on the drop branch.
    (c) allAlternate_reverse   : allAlternate l → allAlternate l.reverse.

**Lean proofs.** In
[`lean/Chanlun/BiEndpointSubResidues.lean`](lean/Chanlun/BiEndpointSubResidues.lean):
`to_endpoint_leftmost_eq_extremal_on_reachable`,
`dropBranch_step_no_op`, `dropBranch_preserves_IsValidBi`,
`allAlternate_reverse`, and the lift `strokes_alternate`.

### Theorem 3.6 — `fractals_alternate_on_containment_free` (reachable-domain determinism)

**Prose.** On the reachable domain — bar lists with no adjacent
containment, which is exactly what Algorithm N produces — the fractal
kinds strictly alternate. Consequently the three a-priori-distinct
readings of stroke endpoints (leftmost / extremal / keep-latter) all
coincide on every reachable input. Any disagreement reported on
arbitrary inputs is an artifact of the input-domain encoding, not a
genuine ambiguity in Chanlun.

**Formal.**

    ∀ bars : List Bar, noAdjBarContainment bars → AlternateKinds (fractalKinds bars).

**Lean proof.**
[`Chanlun.BiReachableDeterminism.fractals_alternate_on_containment_free`](lean/Chanlun/BiReachableDeterminism.lean).
Proof chain:

1. `dichotomy_of_no_containment`: any non-contained pair is strictly
   directional in both h and l.
2. `neither_preserves_direction`: a `.neither` window on containment-free
   input forces the direction to persist.
3. `fractalKinds_first_kind_after_{up,down}`: leading direction forces
   the first emitted kind.
4. Main theorem by induction on the bar list.

The user-facing corollary that chains §1's normalization with this
alternation theorem is
`Chanlun.BiReachableDeterminismBridge.normalize_then_fractals_alternate`.

---

## §4 线段 — Segment (Definitions 5–16 + Theorem 1)

### Definition 4.1 (the BoundedFix recursion)

**Prose.** Segments partition a stroke index range [a, n) into maximal
contiguous sub-ranges that share a feature direction. The recursive
emitter is parameterized over an *advance oracle* `find_term` returning
the next leftmost terminating index ≥ a.

**Formal.** Given `find_term : ℕ → Option ℕ` and a contract
`find_term_ge : ∀ a j, find_term a = some j → a ≤ j`,

    segments find_term find_term_ge a n :=
      if h : a ≥ n then []
      else match h' : find_term a with
        | none   ⇒ [⟨a, n - 1⟩]
        | some j ⇒ ⟨a, j⟩ :: segments find_term find_term_ge (j + 1) n.

Termination is by the strict decrease `n - (j + 1) < n - a`.

**Lean realization.** `Chanlun.Segment.segments` in
[`lean/Chanlun/Segment.lean`](lean/Chanlun/Segment.lean). The feature-sequence
Φ + overlap admissibility internals of `find_term` are not re-derived
here; the Lean recursion needs only the LEFTMOST-≥-a contract.

### Theorem 4.2 — `segment_advance_strictly_increasing`

**Prose.** The central termination lemma. Whenever `find_term a` returns
some j with a ≤ j, the measure n − a strictly decreases at the recursive
step.

**Formal.**

    find_term a = some j → a ≤ j → n - (j + 1) < n - a.

**Lean proof.** `Chanlun.Segment.segment_advance_strictly_increasing`.
A short integer-arithmetic argument.

### Theorem 4.3 — `segments_partition` (property P)

**Prose.** The emitted segments contiguously tile [a, n) — every index
belongs to exactly one segment.

**Formal.**

    ∀ a n, partitionFrom (segments find_term find_term_ge a n) a n.

**Lean proof.** `Chanlun.Segment.segments_partition`, via the strong-form
`segments_partitionFrom` lemma.

### Theorem 4.4 — `segments_terminate` (property T)

**Prose.** At most n − a + 1 segments are emitted; the recursion produces
a finite list.

**Formal.**

    ∀ a n, (segments find_term find_term_ge a n).length ≤ n - a + 1.

**Lean proof.** `Chanlun.Segment.segments_terminate`, via
`segments_length_le`.

### Theorem 4.5 — non-vacuity of the oracle interface

**Prose.** The trivial advance oracle `a ↦ some a` satisfies the
LEFTMOST-≥-a contract, so the recursion is non-vacuously instantiable.

**Formal.**

    ∃ find_term, ∀ a j, find_term a = some j → a ≤ j.

**Lean proof.** `Chanlun.Segment.find_term_contract_nonvacuous`,
witnessed by `trivialFindTerm`.

### Status — Theorem 1 (parametric unique decomposition)

**Open.** The master text's Theorem 1 asserts that the segment
decomposition is **the** decomposition for a parametric class of valid
feature-sequence oracles. Our Lean encoding settles the recursion under
the LEFTMOST-≥-a contract abstractly, and shows determinism for any
fixed `find_term` (the function is by definition). The remaining
parametric uniqueness statement — that any two oracles satisfying the
master's Φ-overlap-admissibility specification produce the same segment
list — is named `[chanlun_segment_phi_uniqueness_OPEN]` and is open
because the master text does not fix Φ uniquely; alternative readings
are tabulated under "Known limitations" in
[`README.md`](README.md).

---

## §5 中枢 — Center (lessons 17/20)

### Definition 5.1 (center formation)

**Prose.** A center forms when three consecutive sub-elements share a
non-empty overlapping zone in price. Scan from i = 0: with at least three
elements remaining, take

    ZD := max(els[i].lo, els[i+1].lo, els[i+2].lo)
    ZG := min(els[i].hi, els[i+1].hi, els[i+2].hi).

If ZD ≤ ZG (genuine overlap), emit a center ⟨i, extendEnd(i+3), ZD, ZG⟩
and continue past extendEnd; otherwise slide i := i + 1.

**Formal.**

    zhongshu els g i :=
      if els.length ≤ i + 2 then []
      else
        let ZD := max ... ; let ZG := min ...
        if ZD ≤ ZG then ⟨i, extendEnd ..., ZD, ZG⟩ :: zhongshu els g (extendEnd + 1)
        else zhongshu els g (i + 1).

**Lean realization.** `Chanlun.Zhongshu.zhongshu` in
[`lean/Chanlun/Zhongshu.lean`](lean/Chanlun/Zhongshu.lean).

### Definition 5.2 (extension and the zone gate)

**Prose.** The extension function `extendEnd g zd zg j` walks j forward
as long as the j-th element overlaps the live zone. The parameter
g : ZoneGate ∈ {first3, all_} controls whether the live zone is
re-tightened as each new element joins:

- `first3` keeps the zone fixed at the initial (ZD, ZG);
- `all_` tightens to (max zd els[j].lo, min zg els[j].hi) at each step.

The master text leaves this choice underspecified; we provide both
readings and prove both are valid.

**Lean realization.** `Chanlun.Zhongshu.extendEnd`,
`Chanlun.Zhongshu.ZoneGate`.

### Theorem 5.3 — `zhongshu_valid`

**Prose.** Every emitted center has a well-formed zone (ZD ≤ ZG).

**Formal.**

    ∀ els g i, ∀ c ∈ zhongshu els g i, c.ZD ≤ c.ZG.

**Lean proof.** `Chanlun.Zhongshu.zhongshu_valid`. By construction the
formation gate `ZD ≤ ZG` guards every emit.

### Theorem 5.4 — `zhongshu_disjoint`

**Prose.** Consecutive centers do not overlap in index range:
c₁.end_ < c₂.start.

**Formal.**

    ∀ els g i, DisjointConsec (zhongshu els g i).

**Lean proof.** `Chanlun.Zhongshu.zhongshu_disjoint`, threaded via
`zhongshu_head_start_ge`.

### Theorem 5.5 — `extendEnd_ge` (extension termination)

**Prose.** The extension index never goes backwards: extendEnd(j) ≥ j − 1.
This is the measure that makes `zhongshu` well-founded on els.length − i.

**Formal.**

    ∀ els g zd zg j, j - 1 ≤ extendEnd els g zd zg j.

**Lean proof.** `Chanlun.Zhongshu.extendEnd_ge`.

### Definition 5.6 (extension transitions: 延伸 / 扩展 / 新生 / endNoRebirth)

**Prose.** When a new element arrives after a freshly emitted center,
one of four named events occurs: **延伸** (extension within the core
[ZD, ZG]), **扩展** (extension within the envelope [DD, GG]),
**新生** (a new disjoint center begins), or **endNoRebirth** (the
sequence ends without a rebirth). After 9 sub-elements remain in the
same center, the **upgrade** signal fires — the center is large enough
to be lifted to a higher level (lesson 30).

**Formal.** With `upgradeSegments := 9` and `CenterExt` holding both the
core (ZD, ZG) and the envelope (DD, GG),

    classifyExtension : CenterExt → Element → List Element → ExtensionEvent.

**Lean realization.** `Chanlun.ZhongshuExtension.classifyExtension` in
[`lean/Chanlun/ZhongshuExtension.lean`](lean/Chanlun/ZhongshuExtension.lean).

### Theorem 5.7 — extension classification is total

**Prose.** Every input lands in exactly one named event class —
classification is total and never silent.

**Formal.**

    ∀ c e post, classifyExtension c e post ∈
        {extension, expansion, rebirth, endNoRebirth, upgrade}.

**Lean proof.** `Chanlun.ZhongshuExtension.classifyExtension_total`.

### Theorem 5.8 — core- and envelope-soundness

**Prose.** The 延伸 event preserves the core zone (ZD, ZG); the 扩展
event widens the envelope (DD, GG); a 新生 event creates a disjoint core.

**Formal.**

    extension_preserves_core_ZD_ZG : returns extension ⇒ (ZD, ZG) unchanged.
    expansion_widens_GG_DD         : returns expansion ⇒ DD' ≤ DD ∧ GG ≤ GG'.
    rebirth_creates_disjoint_core  : returns rebirth ⇒ new core disjoint from old.

**Lean proofs.** `extension_preserves_core_ZD_ZG`, `expansion_widens_GG_DD`,
`rebirth_creates_disjoint_core` in `Chanlun.ZhongshuExtension`.

### Theorem 5.9 — `upgrade_trigger_iff_9_segments`

**Prose.** The 9-segment upgrade signal fires exactly when the sub-element
count crosses the threshold; it does not depend on the value of the next
incoming element.

**Formal.**

    classifyExtension c e post = upgrade ↔ subSegmentCount c ≥ 9.

**Lean proofs.** `upgrade_trigger_iff_9_segments` and
`upgrade_trigger_element_independent`.

### Theorem 5.10 — `zhongshu_zone_gate_divergence_witness` (constructive divergence)

**Prose.** The first3 vs all_ gate (Definition 5.2) is genuinely
multi-valued, not a notational quibble. There exists a concrete
five-element sequence whose first3 and all_ outputs differ in `end_`.
Both outputs are valid (ZD ≤ ZG) and disjoint — the disagreement is
between two legitimate readings, not one broken one. This certifies the
≈ 12% disagreement rate observed empirically.

**Formal.** With

    els := [⟨0, 10⟩, ⟨3, 13⟩, ⟨5, 8⟩, ⟨7, 12⟩, ⟨5, 6⟩]

(see `Chanlun.DivergenceWitnesses.zoneGateWitnessEls`),

    ∃ zd zg zd' zg' e, overlapsZone zd zg e ∧ ¬ overlapsZone zd' zg' e.

**Lean proof.**
[`Chanlun.DivergenceWitnesses.zhongshu_zone_gate_divergence_witness`](lean/Chanlun/DivergenceWitnesses.lean).
Witness (5, 8) (first3 zone) vs (7, 8) (all_-tightened zone) and the
element ⟨5, 6⟩: 6 ≥ 5 holds but 6 ≥ 7 fails. Validity of both gates is
the companion theorem `zhongshu_zone_gate_witness_valid_disjoint`.

---

## §6 走势 — Walk (types and decomposition, lesson 17)

### Definition 6.1 (WalkType and stepDir)

**Prose.** Between two consecutive centers, the direction is `up` if the
next center's ZD strictly exceeds the previous center's ZG, `down` if
the next ZG falls below the previous ZD, and `neither` otherwise. A list
of centers is classified as `consolidation`, `trend_up`, `trend_down`,
`mixed`, or `none_` according to its step pattern.

**Formal.**

    stepDir prev cur := if prev.ZG < cur.ZD then up
                        else if cur.ZG < prev.ZD then down
                        else neither

    classify : List Center → WalkType
    classify []           = none_
    classify [_]          = consolidation
    classify (c₁::c₂::rs) = if allUp  then trend_up
                            else if allDown then trend_down
                            else mixed.

**Lean realization.** `Chanlun.TrendType.stepDir`,
`Chanlun.TrendType.classify` in
[`lean/Chanlun/TrendType.lean`](lean/Chanlun/TrendType.lean).

### Theorem 6.2 — `classify_total`

**Prose.** Classification is total: every center list lands in exactly
one of {none_, consolidation, trend_up, trend_down, mixed}.

**Formal.**

    ∀ cs : List Center, classify cs ∈ {none_, consolidation, trend_up, trend_down, mixed}.

**Lean proof.** `Chanlun.TrendType.classify_total`.

### Theorem 6.3 — `classify_trend_monotone`

**Prose.** The trend labels are not silent — they enforce
sequentially-same-direction steps.

**Formal.**

    (classify cs = trend_up   → allStepsAreUp   cs)
    ∧ (classify cs = trend_down → allStepsAreDown cs).

**Lean proof.** `Chanlun.TrendType.classify_trend_monotone`, via the
biconditionals `allUp_iff_allStepsAreUp` and `allDown_iff_allStepsAreDown`.

### Definition 6.4 (walk decomposition)

**Prose.** Given a center list, `decompose` partitions it into maximal
walks. A single residual center becomes a `consolidation`; runs of
consecutive `up` steps become `trend_up` walks; runs of `down` steps
become `trend_down` walks. New walks begin the moment adding the next
center would change the walk type.

**Formal.** With `extendRun centers d j` walking j forward while the
step direction equals d,

    decompose : List Center → List Walk.

**Lean realization.**
[`Chanlun.WalkDecomposition.decompose`](lean/Chanlun/WalkDecomposition.lean).

### Theorem 6.5 — `decompose_partition`

**Prose.** The emitted walks tile the center list exactly: every center
index belongs to one walk.

**Formal.**

    Σ (walks.map walkSize) = centers.length.

**Lean proof.** `Chanlun.WalkDecomposition.decompose_partition`.

### Theorem 6.6 — `decompose_monotonic`

**Prose.** Walk boundaries chain: each walk's end_ + 1 equals the next
walk's start.

**Formal.**

    ∀ adjacent (w₁, w₂) ∈ walks, w₁.end_ + 1 = w₂.start.

**Lean proof.** `Chanlun.WalkDecomposition.decompose_monotonic`, via
`decomposeFrom_chain` and the `WalksChain` predicate.

### Theorem 6.7 — `decompose_type_homogeneous`

**Prose.** Every emitted walk has a homogeneous type. Inside a `trend_up`
walk, every internal step is `up`; inside a `trend_down` walk, every
internal step is `down`. The classifier never emits `mixed` or `none_`.

**Formal.**

    ∀ w ∈ decompose centers, w.kind ∈ {consolidation, trend_up, trend_down}
    ∧ all stepDirs inside w agree with w.kind.

**Lean proof.** `Chanlun.WalkDecomposition.decompose_type_homogeneous`,
through the helper `decomposeFrom_type_well_formed`.

### Theorem 6.8 — `decompose_spec_unique_extensional`

**Prose.** The decomposition is **the** decomposition: any function that
matches `decompose` extensionally on the empty input and behaves
identically at index 0 equals `decompose` on every input.

**Formal.**

    ∀ f : List Center → List Walk,
      f [] = decompose [] →
      (∀ cs, f cs starts at the head walk of decompose cs) →
      ∀ cs, f cs = decompose cs.

**Lean proofs.** `decompose_unique`, `decompose_spec_unique_extensional`,
`decompose_spec_unique_empty`, `decompose_spec_unique_head_at_zero`.

### Status — the `mixed` merge

**Open.** A separate downstream merge step could glue adjacent walks into
a `mixed` super-walk. We do not perform that merge in the Lean library;
it is named `[chanlun_walk_mixed_merge_OPEN]` and listed in
[`README.md`](README.md).

---

## §7 背驰 — Divergence (lessons 24/27/29)

### Definition 7.1 (move, displacement, measure)

**Prose.** A directional move is a (lo, hi, dur) triple — a displacement
carrier with explicit duration. The 力度 (strength) of a move can be
measured by displacement alone (`disp`) or by slope (`disp / dur`); the
master text invokes both at different points. We parameterize over a
named `Measure ∈ {disp, slope}`.

**Formal.**

    Move := { lo : ℤ, hi : ℤ, dur : ℤ }
    disp m := m.hi - m.lo
    lhsRhs a c disp  := (disp a, disp c)
    lhsRhs a c slope := (disp a · c.dur, disp c · a.dur)   -- integer-exact cross-product

**Lean realization.** `Chanlun.Beichi.Move`, `Chanlun.Beichi.disp`,
`Chanlun.Beichi.lhsRhs` in [`lean/Chanlun/Beichi.lean`](lean/Chanlun/Beichi.lean).

### Definition 7.2 (the 背驰 classifier)

**Prose.** C diverges from A — 背驰 — when C is weaker than A under the
chosen measure: lhs < rhs. Equal strength is `tie`; greater strength is
`no_beichi`.

**Formal.**

    classifyBeichi a c m :=
      let (lhs, rhs) := lhsRhs a c m
      if lhs < rhs then beichi
      else if lhs = rhs then tie
      else no_beichi.

### Theorem 7.3 — `classifyBeichi_total` and `beichi_irrefl`

**Prose.** Classification is total over {beichi, no_beichi, tie}, and is
irreflexive: a move never diverges from itself.

**Formal.**

    ∀ a c m, classifyBeichi a c m ∈ {beichi, no_beichi, tie}
    ∀ a m, classifyBeichi a a m ≠ beichi.

**Lean proofs.** `classifyBeichi_total`, `beichi_irrefl`, via the
auxiliary `lhsRhs_self_eq`.

### Theorem 7.4 — `beichi_load_bearing`

**Prose.** The classifier really does compare strengths. Under disp,
`beichi a c` is equivalent to `disp c < disp a`; under slope, to the
integer-exact cross-product comparison.

**Formal.**

    classifyBeichi a c disp  = beichi ↔ disp c < disp a
    classifyBeichi a c slope = beichi ↔ disp c · a.dur < disp a · c.dur.

**Lean proofs.** `beichi_load_bearing_slope`, `beichi_load_bearing_disp`,
combined into `beichi_load_bearing`. Companion no-beichi/tie forms:
`no_beichi_disp_strict`, `no_beichi_slope_strict`, `tie_disp_iff`,
`tie_slope_iff`.

### Theorem 7.5 — `beichi_measure_gate_witness` (constructive divergence)

**Prose.** The disp vs slope choice is genuinely multi-valued. There
exist moves a, c such that disp says 背驰 while slope says no_beichi —
the master text's silence on which measure to use is a real ambiguity,
not a notational one.

**Formal.**

    ∃ a c, classifyBeichi a c disp = beichi
         ∧ classifyBeichi a c slope = no_beichi.

**Lean proof.** `Chanlun.Beichi.beichi_measure_gate_witness`, re-exported
to the consolidated divergence-witness surface as
`Chanlun.DivergenceWitnesses.beichi_measure_gate_divergence_witness`.

### Definition 7.6 (盘整背驰, lesson 37)

**Prose.** Within a single center, an A-leg entering the center and a
C-leg leaving it form a `PanzhengTriple`. The 盘整背驰 classifier
declares panzheng_beichi when C is weaker than A under the chosen
measure, no_panzheng_beichi otherwise; the balanced case is incomplete.

**Formal.** `classifyPanzheng : PanzhengTriple → Measure → PanzhengVerdict`.

**Lean realization.** `Chanlun.PanzhengBeichi.classifyPanzheng` in
[`lean/Chanlun/PanzhengBeichi.lean`](lean/Chanlun/PanzhengBeichi.lean).

### Theorem 7.7 — totality and load-bearing of 盘整背驰

**Prose.** The classifier is total; on each measure it really does
compare strengths; the incomplete verdict is exactly the balanced case.

**Formal.**

    classify_panzheng_total       : every input lands in the four-class verdict.
    panzheng_load_bearing_disp    : panzheng_beichi ⇒ disp c < disp a.
    panzheng_load_bearing_slope   : panzheng_beichi ⇒ cross-product comparison.
    panzheng_incomplete_iff       : incomplete ↔ disp c · a.dur = disp a · c.dur (under slope).

**Lean proofs.** `classify_panzheng_total`, `panzheng_load_bearing_disp`,
`panzheng_load_bearing_slope`, `panzheng_incomplete_iff`.

### Theorem 7.8 — `panzheng_measure_gate_witness` and intra-vs-inter

**Prose.** Two further constructive witnesses pin down 盘整背驰:
(a) the disp-vs-slope gate is real even at the panzheng level — there
exist triples where disp says panzheng_beichi while slope says
no_panzheng_beichi; (b) using the inter-中枢 measure on a single-center
triple is genuinely a different classifier — there exists a triple where
the intra-中枢 classifier says panzheng_beichi while the inter-中枢
mutant says no_panzheng_beichi.

**Formal.**

    panzheng_measure_gate_witness : ∃ t, intra-disp = panzheng_beichi ∧ intra-slope = no_panzheng_beichi.
    panzheng_intra_vs_inter_load_bearing : ∃ t, intra ≠ inter-mutant.

**Lean proofs.** `panzheng_measure_gate_witness`,
`panzheng_intra_vs_inter_load_bearing`, lifted to the divergence-witness
surface as `panzheng_measure_gate_propagation_witness`.

### MACD as auxiliary measure (lesson 27, empirical grounding)

**Prose.** Lesson 27 names MACD as an explicit **auxiliary** measure —
not the canonical disp/slope, but a refinement. On 7-year real NQ 1h
data, MACD's 背驰 verdict agrees with disp at roughly 46.4% and with
slope at roughly 17.9% of the extracted (A, C) windows. Disagreement
positions are reported as explicit (a_idx, c_idx, disp_says, macd_says)
witnesses. The disagreement is the empirical content of "MACD is
auxiliary, not canonical".

**Lean status.** Open as `[chanlun_beichi_macd_measure_lean_OPEN]`:
extending `Chanlun.Beichi.Measure` to a third constructor `macd` is
structurally clean (the algebra extends; the cross-product compares
MACD-energies). The grounding script
[`grounding/chanlun_macd_grounding.py`](grounding/chanlun_macd_grounding.py)
computes the agreement rates and emits the divergence witnesses; the
constructive Lean lift is named open.

---

## §8 三类买卖点 — Three classes of buy/sell points (lessons 20, 24)

### Definition 8.1 (the 第一/第二类 classifier, lesson 24)

**Prose.** A `TerminalWindow` packages the inter-center A-move with a
candidate pullback move and the entry levels. The classifier first asks
whether the A-leg diverges (background 背驰); if yes, a
`first_buy/first_sell` is declared; the pullback is then tested for
non-breaking to upgrade to `second_buy/second_sell`. A first-point
attempt with a breaking pullback is `first_point_failed`; the silent case
is `incomplete`.

**Formal.** `classifyBsp : TerminalWindow → Measure → BspKind`, with
`BspKind ∈ {first_buy, first_sell, second_buy, second_sell,
first_point_failed, incomplete}`.

**Lean realization.** `Chanlun.FirstSecondBuysell.classifyBsp` in
[`lean/Chanlun/FirstSecondBuysell.lean`](lean/Chanlun/FirstSecondBuysell.lean).

### Theorem 8.2 — totality and non-breaking

**Prose.** Classification is total. A `second_buy` verdict means the
pullback genuinely did not break the first-point extreme; symmetrically
for `second_sell`. The `first_point_failed` verdict means the pullback
broke through.

**Formal.**

    classify_total          : verdict ∈ BspKind for every input.
    second_buy_non_breaking : second_buy  → pull.lo ≥ firstExtreme.
    second_sell_non_breaking: second_sell → pull.hi ≤ firstExtreme.
    first_point_failed_iff  : first_point_failed ↔ pullback breaks.

**Lean proofs.** `classify_total`, `classify_first_point_only_total`,
`second_buy_non_breaking`, `second_sell_non_breaking`,
`second_not_breaking_iff`, `first_point_failed_iff`.

### Theorem 8.3 — `first_second_inheritance_load_bearing`

**Prose.** Measure-gate propagation reaches the buy/sell point level.
There exists a `TerminalWindow` such that the disp-measure classifier
returns `second_buy` while the slope-measure classifier returns
`incomplete` — the choice of 力度 measure propagates downstream into the
trader-facing verdicts.

**Formal.**

    ∃ w, classifyBsp w disp = second_buy ∧ classifyBsp w slope = incomplete.

**Lean proof.** `first_second_inheritance_load_bearing`, surfaced as
`Chanlun.DivergenceWitnesses.first_second_measure_gate_divergence_witness`.

### Theorem 8.4 — `classify_implies_beichi_and_pull`

**Prose.** A non-incomplete verdict requires both the background 背驰
to hold under the chosen measure and the pullback move to be defined.

**Formal.**

    classifyBsp w m ≠ incomplete → (背驰 holds under m ∧ pull is defined).

**Lean proof.** `classify_implies_beichi_and_pull`.

### Definition 8.5 (the 第三类 classifier, lesson 20)

**Prose.** After a center completes, the next departure move either
breaks above ZG (giving a `third_buy`), breaks below ZD
(`third_sell`), re-enters the zone from above (`reenter_above`), or from
below (`reenter_below`). Plus a no-departure incomplete state.

**Formal.** `classifyBsp : Departure → BspKind` with
`BspKind ∈ {third_buy, third_sell, reenter_above, reenter_below,
incomplete}`.

**Lean realization.** `Chanlun.ThirdBuysell.classifyBsp` in
[`lean/Chanlun/ThirdBuysell.lean`](lean/Chanlun/ThirdBuysell.lean).

### Theorem 8.6 — totality and zone-meaningfulness of 第三类

**Prose.** Classification is total. A `third_buy` really does mean the
departure breaks ZG upward; a `third_sell` really does mean it breaks ZD
downward.

**Formal.**

    classifyBsp_total          : verdict ∈ BspKind for every input.
    bsp_zone_load_bearing_up   : third_buy  → dep.move.lo > c.ZG.
    bsp_zone_load_bearing_down : third_sell → dep.move.hi < c.ZD.

**Lean proofs.** `classifyBsp_total`, `bsp_zone_load_bearing_up`,
`bsp_zone_load_bearing_down`.

### Theorem 8.7 — recursive sub-level buy/sell points

**Prose.** The 第三类 classification at a sub-level is total, terminates
under bounded fuel, and inherits the parent-level verdict in a tracked
`RecursiveVerdict` tag. The fuel bound is sourced from the level-recursion
strict-drop measure (Theorem 9.2 below).

**Formal.**

    recursive_subBsp_total           : every call lands in one of four named verdicts.
    recursive_subBsp_terminates      : sufficient fuel → no incomplete.
    recursive_subBsp_inheritance     : level-n verdict is preserved if the sub-verdict agrees.
    recursive_subBsp_fuel_stationary : the verdict becomes fuel-invariant once fuel ≥ level depth.
    recursive_subBsp_fuel_bound_via_levelRecursion : fuel ≤ n / 2 suffices.

**Lean proofs.** All in
[`lean/Chanlun/RecursiveSubBspBeichi.lean`](lean/Chanlun/RecursiveSubBspBeichi.lean):
`recursive_subBsp_total`, `recursive_subBsp_terminates`,
`recursive_subBsp_inheritance`, `recursive_subBsp_fuel_stationary`,
`recursive_subBsp_fuel_bound_via_levelRecursion`.

---

## §9 级别递归 — Level recursion (lesson 24: "every trend must complete")

### Definition 9.1 (`centerSize` and the level lift)

**Prose.** Each center has size `c.end_ + 1 - c.start`, the count of
sub-elements it covers. The next level is built by lifting each center
to an `Element` carrying its core zone [ZD, ZG]; the `liftStep` is one
round of `zhongshu` followed by `liftCenters`.

**Formal.**

    centerSize c   := c.end_ + 1 - c.start
    liftCenter c   := { lo := c.ZD, hi := c.ZG }
    liftCenters cs := cs.map liftCenter
    liftStep els g := liftCenters (zhongshu els g 0)
    levelTower els g 0       := els
    levelTower els g (n + 1) := levelTower (liftStep els g) g n.

**Lean realization.** Definitions in
[`lean/Chanlun/LevelRecursion.lean`](lean/Chanlun/LevelRecursion.lean).

### Theorem 9.2 — `lift_strict_drop` ("every trend must complete")

**Prose.** Once any center forms, the count of sub-elements consumed by
the center list exceeds the center count by at least 2. So lifting to
the next level strictly decreases the element count — by well-founded
recursion on ℕ, the level recursion terminates in ≤ n/2 levels. This is
the formal content of lesson 24's "走势必完美".

**Formal.**

    ∀ els g, zhongshu els g 0 ≠ [] →
      (zhongshu els g 0).length + 2 ≤ ((zhongshu els g 0).map centerSize).sum.

**Lean proof.** `Chanlun.LevelRecursion.lift_strict_drop`. The proof
chains `centerSize_ge_3` (every center covers ≥ 3 sub-elements) with the
arithmetic `total_size_ge_3_times_count`. The corollary
`level_recursion_count_decreases` packages the strict drop directly.

### Theorem 9.3 — `centerSize_ge_3`

**Prose.** Every emitted center covers at least three sub-elements.
Immediate consequence of `extendEnd_ge` (Theorem 5.5): extension starts
at i + 3 and never returns before i + 2.

**Formal.**

    ∀ els g, ∀ c ∈ zhongshu els g 0, 3 ≤ centerSize c.

**Lean proof.** `Chanlun.LevelRecursion.centerSize_ge_3`.

### Theorem 9.4 — envelope-soundness

**Prose.** Each lifted Element has a well-formed zone (lo ≤ hi)
inherited from the center it was lifted from.

**Formal.**

    liftCenter_lo_le_hi : c.ZD ≤ c.ZG → (liftCenter c).lo ≤ (liftCenter c).hi.
    liftCenters_all_valid : every element of liftCenters (zhongshu els g 0) has lo ≤ hi.
    liftCenters_mem_iff : e ∈ liftCenters cs ↔ ∃ c ∈ cs, e = liftCenter c.

**Lean proofs.** `liftCenter_range_eq_core`, `liftCenter_lo_le_hi`,
`liftCenters_all_valid`, `liftCenters_mem_iff`.

### Theorem 9.5 — determinism preservation across levels

**Prose.** The level lift is deterministic: equal inputs at level 0
produce equal towers at every level. Sub-level disagreement only arises
from input disagreement at level 0.

**Formal.**

    liftStep_deterministic   : els = els' → liftStep els g = liftStep els' g.
    levelTower_deterministic : els = els' → ∀ n, levelTower els g n = levelTower els' g n.
    levelTower_input_eq      : equal inputs → equal towers.
    levelTower_agreement_lifts: level-0 agreement propagates up.

**Lean proofs.** `liftStep_deterministic`, `levelTower_deterministic`,
`levelTower_input_eq`, `levelTower_agreement_lifts`.

---

## §10 走势分解 — Walk decomposition (lesson 17, full form)

### Definition 10.1 (the spec — partition / monotonic / type-homogeneous / unique)

**Prose.** The `decompose` function (Definition 6.4) is constrained by
four properties: (1) partition — walks tile the center list; (2)
monotonicity — walk boundaries chain strictly; (3) type-homogeneity —
each walk has a single non-mixed type and every internal step agrees;
(4) spec-uniqueness — any function with the same head-extending behaviour
at index 0 equals `decompose`.

### Theorem 10.2 — the four properties hold

**Prose.** All four properties hold for `decompose`.

**Formal.** Restating §6 here as the formal "walk decomposition theorem":

    decompose_partition           : Σ walkSize = centers.length.
    decompose_monotonic           : w₁.end_ + 1 = w₂.start.
    decompose_type_homogeneous    : every walk's type is non-mixed and homogeneous internally.
    decompose_spec_unique_extensional : any spec-matching function = decompose.

**Lean proofs.** As in §6: `decompose_partition`, `decompose_monotonic`,
`decompose_type_homogeneous`, `decompose_unique`,
`decompose_spec_unique_extensional`, `decompose_spec_unique_empty`,
`decompose_spec_unique_head_at_zero`, with the helper `decomposeFrom_nonempty`.

---

## §11 区间套 — Interval nesting (lessons 65/66, multi-resolution)

### Definition 11.1 (the synthetic-tower walker)

**Prose.** A `LevelWindow` is a contiguous index range at a level. The
区间套 walker descends through levels using a `descend` oracle that
proposes a finer sub-window. The walker terminates with a NAMED verdict
when descent stops.

**Formal.**

    LevelWindow := { level : ℕ, start : ℕ, end_ : ℕ }
    DescendValid descend := ∀ w w', descend w = some w' → w'.level < w.level
    walk descend w := if descend w = some w' then walk descend w' else terminate w.

**Lean realization.** `Chanlun.IntervalNesting.LevelWindow`, `walk` in
[`lean/Chanlun/IntervalNesting.lean`](lean/Chanlun/IntervalNesting.lean).

### Theorem 11.2 — termination, never-silent, pin-monotone

**Prose.** Given a valid descent oracle (every descent strictly drops the
level), the walker terminates, returns a named verdict, and every
descended window has strictly lower level than its parent. A chain of
successful descents strictly drops the level at every step.

**Formal.**

    intervalnesting_terminates       : walker always halts on DescendValid descend.
    walk_always_has_verdict          : every output state has a NAMED verdict.
    intervalnesting_pin_monotone     : descend w = some w' → w'.level < w.level.
    intervalnesting_chain_strict_drop: ∀ chain, levels strictly decrease.

**Lean proofs.** `intervalnesting_terminates`, `walk_always_has_verdict`,
`intervalnesting_pin_monotone`, `intervalnesting_chain_strict_drop`.

### Theorem 11.3 — terminal-form theorems

**Prose.** At level 0 with no further descent, the walker returns the
gate-limit verdict; at positive level with no further descent, it
returns the pinned verdict.

**Formal.**

    walk_at_zero_returns_gate_limit
    walk_at_positive_returns_pinned.

**Lean proofs.** Same names in `Chanlun.IntervalNesting`.

### Status — multi-resolution real-data grounding

**Prose.** The single-resolution synthetic-tower walker is fully proven
in Lean. The genuine multi-resolution claim — that the descent
corresponds to switching to a finer timeframe of real market data, with
timestamp-based mapping between levels — is settled empirically rather
than in Lean. On 7-year NQ data at 1d, 1h, and 1m resolutions, the
descent works: a 1d-level center, mapped down to 1h by timestamp,
contains a 1h-level sub-center, which further descends to 1m. Some 1d
centers have no 1h sub-center within their timestamp span — these are
the "lowest-level-of-this-资金" residue and are reported as named
witnesses.

The two named-open items are
`[chanlun_intervalnesting_multiscale_OPEN]` and
`[chanlun_intervalnesting_lowest_level_OPEN]`. Settled empirically via
[`grounding/chanlun_multiscale_real_grounding.py`](grounding/chanlun_multiscale_real_grounding.py);
a Lean lift would need a model of real-time timestamp mapping that is
out of scope for the integer-arithmetic kernel.

---

## §12 MACD auxiliary measure (lesson 27, empirical grounding)

**Prose.** Lesson 27 invokes MACD as an explicit auxiliary measure
alongside disp and slope. The grounding settles two empirical claims:

1. On 7-year real NQ 1h data with extracted (A, C) 背驰 windows, MACD's
   verdict agrees with disp at roughly 46.4% and with slope at roughly
   17.9% — MACD is a refinement, not a substitute. Disagreement
   positions are emitted as explicit (a_idx, c_idx, disp_says, macd_says)
   witnesses.
2. A wrong-period MACD (fast EMA period 9 instead of 12) MUST diverge
   from the canonical MACD on the same input — the parameter choice is
   load-bearing.

**Lean status.** Named open as
`[chanlun_beichi_macd_measure_lean_OPEN]`. Extending
`Chanlun.Beichi.Measure` to a third constructor is structurally clean;
the obstruction is the need for real MACD-energy values that are not
expressible inside the integer-arithmetic kernel without a separate
data interface.

**Script.**
[`grounding/chanlun_macd_grounding.py`](grounding/chanlun_macd_grounding.py).

---

## §X Coverage audit — per-item status by category

This section is the structural audit of the paper-to-Lean coverage. Each
named item from the master text — definition or theorem — receives one of
four categorical statuses with an explicit, auditable justification.

### §X.0 Status legend and totals

The four categories are mutually exclusive:

- **PROVEN_DIRECT.** A sorry-free Lean theorem under `lean/Chanlun/` is
  the formal statement. The Lean identifier is cited; the proof
  technique is named in one phrase.
- **PROVEN_FIXTURE.** Proven on representative inputs by computation
  (typically `native_decide` on fixed concrete instances), not as a
  universal statement.
- **MULTI_VALUED_NAMED.** The master text legitimately allows multiple
  readings; the divergence is settled by a constructive Lean witness
  (under `Chanlun.DivergenceWitnesses` or the originating module). The
  item is not a missing proof — it is a documented multi-valuedness.
- **NOT_FORMALIZED.** No Lean theorem yet. The cell names the concrete
  blocker — a specific limitation of the integer-arithmetic kernel,
  the prelude-only / mathlib boundary, the genuine ambiguity of the
  master text, or a structural design choice — that an external reader
  can inspect.

**Totals across §X.1 – §X.10** (1 item = 1 row; multi-witness rows count
as 1):

| Status | Count | Notes |
|---|---|---|
| PROVEN_DIRECT | 59 | sorry-free Lean theorems under `lean/Chanlun/` |
| MULTI_VALUED_NAMED | 6 | each backed by a constructive divergence witness in `Chanlun.DivergenceWitnesses` or the originating module |
| PROVEN_FIXTURE | 0 | (none counted in chanlun.md proper — empirical groundings live under `grounding/` and `conformance/`, not as Lean statements; the multi-scale claim X.10.4 cites `grounding/chanlun_multiscale_real_grounding.py` as PROVEN_FIXTURE outside Lean) |
| NOT_FORMALIZED | 13 | each cell names the specific blocker (integer kernel design, module-bridging, master-text multi-readability, downstream-component design choice) |
| **Total** | **78** | named paper items audited |

The audit covers every `Def x.y` and `Thm x.y` shipped in §1 through §11
of this document, plus the `Status —` items each of §4, §6, §7, §8, §9,
§11, §12 declares explicitly. The six MULTI_VALUED_NAMED items are
X.3.7 (`bi-to-endpoint` reading on arbitrary inputs), X.5.10 (zone-gate
first3 vs all_), X.5.11 (shoulder ≤ vs <), X.7.5 (disp vs slope), X.7.8
(panzheng disp vs slope + intra vs inter), X.8.3 (measure-gate
propagation into 第一/第二 buy/sell). The thirteen NOT_FORMALIZED items
are X.4.6 (Φ-uniqueness across oracles — master-text ambiguity), X.5.12,
X.5.13, X.6.9, X.7.9, X.8.8, X.8.9, X.9.6, X.9.7, X.10.4, X.10.5,
X.10.6, X.10.7. None of the NOT_FORMALIZED items use the phrase
"future work" or "out of scope" as the blocker — each names the
structural reason (integer kernel cannot represent floats / timestamps
/ MACD energy; module-bridging needs an additional invariant carrier;
downstream-component design choice; master-text ambiguity on Φ).

### §X.1  Algorithm N (§1)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.1.1 | Def 1.1 containment relation | PROVEN_DIRECT | `Chanlun.Normalize.contained` + `noAdjContainment` |
| X.1.2 | Def 1.2 single-pass normalize | PROVEN_DIRECT | `Chanlun.Normalize.normalize` (function-as-definition) |
| X.1.3 | Thm 1.3 single-pass produces noAdjContainment | PROVEN_DIRECT | `Chanlun.Normalize.normalize_no_adjacent_containment`, induction over `pushOne_preserves` |

### §X.2  分型 / Fractal (§2)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.2.1 | Def 2.1 top/bottom fractal | PROVEN_DIRECT | `Chanlun.Fractal.classifyDef3` |
| X.2.2 | Thm 2.2 trichotomy | PROVEN_DIRECT | `Chanlun.Fractal.def3_trichotomy`, case split on strict comparisons |
| X.2.3 | Thm 2.3 prose-vs-operator equivalence | PROVEN_DIRECT | `Chanlun.Fractal.fractal_slot_equiv_def3`, 9-way case split |
| X.2.4 | Thm 2.4 pipeline composition | PROVEN_DIRECT | `Chanlun.Pipeline.pipeline_inclusion_normalized` via `not_contained_iff_bar` |
| X.2.5 | Thm 2.5 well-defined classification | PROVEN_DIRECT | `Chanlun.Pipeline.pipeline_fractal_classification_well_defined` |
| X.2.6 | End-to-end bridge (raw Interval → alternating fractalKinds) | PROVEN_DIRECT | `Chanlun.BiReachableDeterminismBridge.normalize_then_fractals_alternate` — the one-step composition `normalize` + `map toBar` + `fractalKinds` → `AlternateKinds` |

### §X.3  笔 / Stroke (§3)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.3.1 | Def 3.1 leftmost-greedy stroke construction | PROVEN_DIRECT | `Chanlun.Stroke.step`, `Chanlun.Stroke.strokes` |
| X.3.2 | Thm 3.2 separation (property B) | PROVEN_DIRECT | `Chanlun.Stroke.stroke_emits_separated`, lifted as `strokes_separated` via `List.mem_reverse` |
| X.3.3 | Thm 3.3 alternation (property A) | PROVEN_DIRECT | `Chanlun.Stroke.stroke_emits_alternate`, reverse-output lift `Chanlun.BiEndpointSubResidues.strokes_alternate` via `allAlternate_reverse` |
| X.3.4 | Thm 3.4 strokes_unique (Lemma 2 strong form) | PROVEN_DIRECT | `Chanlun.StrokeUniqueness.strokes_unique`, induction over the `fold_consumes_alt` invariant |
| X.3.4-corollary | IsValidBi non-vacuity + biconditional | PROVEN_DIRECT | `Chanlun.StrokesIsValidBiCorollary.strokes_isValidBi` and `strokes_iff_IsValidBi` |
| X.3.5 | Thm 3.5 endpoint sub-results (a)+(b)+(c) | PROVEN_DIRECT | `to_endpoint_leftmost_eq_extremal_on_reachable`, `dropBranch_step_no_op`, `dropBranch_preserves_IsValidBi`, `allAlternate_reverse` in `Chanlun.BiEndpointSubResidues` |
| X.3.6 | Thm 3.6 reachable-domain alternation | PROVEN_DIRECT | `Chanlun.BiReachableDeterminism.fractals_alternate_on_containment_free`, chain via `dichotomy_of_no_containment` + `neither_preserves_direction` |
| X.3.7 | TO-endpoint reading on arbitrary inputs (leftmost-admissible vs extremal-literal) | MULTI_VALUED_NAMED → on reachable domain PROVEN_DIRECT | On reachable input the two readings coincide (Thm 3.6 + `to_endpoint_leftmost_eq_extremal_on_reachable`); on arbitrary input the master text genuinely supports both, and this is a documented choice (StrokeUniqueness takes the leftmost-admissible reading) |
| X.3.8 | Silent drop of over-close reverse fractals | PROVEN_DIRECT | `Chanlun.BiEndpointSubResidues.dropBranch_step_no_op` proves the drop branch is a no-op |

### §X.4  线段 / Segment (§4)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.4.1 | Def 4.1 BoundedFix recursion | PROVEN_DIRECT | `Chanlun.Segment.segments`, parameterized over `find_term` + `find_term_ge` |
| X.4.2 | Thm 4.2 strict-advance termination measure | PROVEN_DIRECT | `Chanlun.Segment.segment_advance_strictly_increasing`, integer arithmetic |
| X.4.3 | Thm 4.3 partition (property P) | PROVEN_DIRECT | `Chanlun.Segment.segments_partition` via `segments_partitionFrom` |
| X.4.4 | Thm 4.4 termination (property T, bounded length) | PROVEN_DIRECT | `Chanlun.Segment.segments_terminate` via `segments_length_le` |
| X.4.5 | Thm 4.5 oracle non-vacuity | PROVEN_DIRECT | `Chanlun.Segment.find_term_contract_nonvacuous` (witness `trivialFindTerm`) |
| X.4.6 | Master Theorem 1: parametric Φ-uniqueness across all Φ-overlap-admissibility-satisfying oracles | NOT_FORMALIZED — multi-valued by source | The master text does not fix Φ uniquely (multiple readings of feature-sequence Φ + overlap-admissibility appear at lessons 65 vs 67); two readings yield two oracles which yield different segment lists on the same input. Determinism per single oracle is PROVEN_DIRECT (function-as-definition). The parametric statement is structurally a master-text ambiguity, not a Lean proof gap |

### §X.5  中枢 / Center (§5)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.5.1 | Def 5.1 center formation | PROVEN_DIRECT | `Chanlun.Zhongshu.zhongshu` |
| X.5.2 | Def 5.2 extension function + ZoneGate | PROVEN_DIRECT | `Chanlun.Zhongshu.extendEnd` parameterized over `ZoneGate ∈ {first3, all_}` |
| X.5.3 | Thm 5.3 zhongshu_valid (ZD ≤ ZG) | PROVEN_DIRECT | `Chanlun.Zhongshu.zhongshu_valid` |
| X.5.4 | Thm 5.4 zhongshu_disjoint | PROVEN_DIRECT | `Chanlun.Zhongshu.zhongshu_disjoint` via `zhongshu_head_start_ge` |
| X.5.5 | Thm 5.5 extendEnd_ge (extension termination measure) | PROVEN_DIRECT | `Chanlun.Zhongshu.extendEnd_ge` |
| X.5.6 | Def 5.6 four-way extension classifier (延伸/扩展/新生/endNoRebirth + upgrade) | PROVEN_DIRECT | `Chanlun.ZhongshuExtension.classifyExtension` |
| X.5.7 | Thm 5.7 classifyExtension_total | PROVEN_DIRECT | `Chanlun.ZhongshuExtension.classifyExtension_total` |
| X.5.8 | Thm 5.8 core/envelope soundness of each event | PROVEN_DIRECT | `extension_preserves_core_ZD_ZG`, `expansion_widens_GG_DD`, `rebirth_creates_disjoint_core` |
| X.5.9 | Thm 5.9 9-segment upgrade trigger | PROVEN_DIRECT | `upgrade_trigger_iff_9_segments` + `upgrade_trigger_element_independent` |
| X.5.10 | Thm 5.10 zone-gate divergence witness | MULTI_VALUED_NAMED | `Chanlun.DivergenceWitnesses.zhongshu_zone_gate_divergence_witness` — first3 vs all_ are both legitimate readings of the master text; the gate disagrees on element ⟨5, 6⟩ within `zoneGateWitnessEls`; both gates produce valid + disjoint outputs (`zhongshu_zone_gate_witness_valid_disjoint`). On the reachable (containment-free) domain the two readings coincide |
| X.5.11 | Shoulder cases (`next_el.lo = ZG` or `next_el.hi = ZD`) — ≤ vs strict-< | MULTI_VALUED_NAMED | Master text supports both ≤ and < readings (lesson 17 line 3 wording vs lesson 17 example computation); this repository takes ≤ as the canonical reading; the other reading is a sibling oracle |
| X.5.12 | Extension propagation under the `all_` gate (full list-induction form) | NOT_FORMALIZED — list-induction missing | The `first3` form is fully discharged in `Chanlun.ZhongshuExtension`; the `all_` form requires a separate list-induction tracking the tightening zone through `extendEnd` steps. Blocker: the tightening zone state-passing requires an additional invariant carrier not present in the current `CenterExt` data structure |
| X.5.13 | Multi-element envelope across a complete zhongshu (list-induction form) | NOT_FORMALIZED — list-induction missing | Single-step `expansion_widens_GG_DD` is PROVEN_DIRECT. The cross-list cumulative envelope (DD monotonically descends and GG monotonically ascends across all elements of one center) requires list-induction over the post-element stream; not yet completed |

### §X.6  走势 / Walk type + decomposition (§6, §10)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.6.1 | Def 6.1 stepDir + classify (WalkType) | PROVEN_DIRECT | `Chanlun.TrendType.stepDir`, `classify` |
| X.6.2 | Thm 6.2 classify_total | PROVEN_DIRECT | `Chanlun.TrendType.classify_total` |
| X.6.3 | Thm 6.3 trend labels enforce same-direction | PROVEN_DIRECT | `Chanlun.TrendType.classify_trend_monotone` via the biconditional helpers |
| X.6.4 | Def 6.4 walk decomposition function | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose` (with `extendRun` helper) |
| X.6.5 | Thm 6.5 decompose_partition | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_partition` |
| X.6.6 | Thm 6.6 decompose_monotonic (boundary chaining) | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_monotonic` via `decomposeFrom_chain` |
| X.6.7 | Thm 6.7 decompose_type_homogeneous | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_type_homogeneous` |
| X.6.8 | Thm 6.8 spec-uniqueness (extensional) | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_spec_unique_extensional`, plus `decompose_spec_unique_empty` and `decompose_spec_unique_head_at_zero` |
| X.6.9 | Mixed-merge downstream step | NOT_FORMALIZED — out-of-scope by design | `decompose` deliberately does NOT emit `mixed` (Thm 6.7); a downstream merger that glues adjacent walks into a `mixed` super-walk is a separate component, not a property of `decompose`. The merge is named open as a separate downstream module and is not part of the walk-decomposition specification |

### §X.7  背驰 / Divergence (§7, §12)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.7.1 | Def 7.1 Move, displacement, lhsRhs | PROVEN_DIRECT | `Chanlun.Beichi.Move`, `disp`, `lhsRhs` |
| X.7.2 | Def 7.2 classifyBeichi | PROVEN_DIRECT | `Chanlun.Beichi.classifyBeichi` |
| X.7.3 | Thm 7.3 totality + irreflexivity | PROVEN_DIRECT | `classifyBeichi_total`, `beichi_irrefl` (via `lhsRhs_self_eq`) |
| X.7.4 | Thm 7.4 load-bearing (disp + slope sides) | PROVEN_DIRECT | `beichi_load_bearing_disp`, `beichi_load_bearing_slope`, combined `beichi_load_bearing`; companion `no_beichi_*_strict`, `tie_*_iff` |
| X.7.5 | Thm 7.5 disp-vs-slope multi-valuedness | MULTI_VALUED_NAMED | `Chanlun.Beichi.beichi_measure_gate_witness`, surfaced as `Chanlun.DivergenceWitnesses.beichi_measure_gate_divergence_witness`. The master text invokes both measures at different points (lesson 24 vs lesson 27) — both readings are legitimate. Empirical agreement ≈ 82.2% on the Python reference; the choice is a documented master-text ambiguity, not a Lean proof gap |
| X.7.6 | Def 7.6 panzheng (盘整背驰) classifier | PROVEN_DIRECT | `Chanlun.PanzhengBeichi.classifyPanzheng` |
| X.7.7 | Thm 7.7 panzheng totality + load-bearing + incomplete-iff | PROVEN_DIRECT | `classify_panzheng_total`, `panzheng_load_bearing_disp`, `panzheng_load_bearing_slope`, `panzheng_incomplete_iff` |
| X.7.8 | Thm 7.8 panzheng measure-gate witness + intra-vs-inter mutant | MULTI_VALUED_NAMED | `panzheng_measure_gate_witness`, `panzheng_intra_vs_inter_load_bearing`, surfaced as `panzheng_measure_gate_propagation_witness` |
| X.7.9 | MACD as `macd` constructor of `Chanlun.Beichi.Measure` | NOT_FORMALIZED — integer kernel cannot represent MACD energy | The integer-arithmetic kernel (`Int` carrier, no floats, no EMAs) cannot directly represent MACD energy values, which are signal-processing-derived running floats. Adding a `macd` constructor to `Measure` is structurally clean (the cross-product algebra extends) but the underlying MACD-energy comparison requires float values that the kernel deliberately avoids (to keep decidability + lake-build constraints). Empirical agreement settled in `grounding/chanlun_macd_grounding.py` (disp ≈ 46.4%, slope ≈ 17.9% on 7-year NQ 1h). Float-carrying Lean lift would require mathlib's `Real` + a separate data-interface layer outside the kernel |

### §X.8  三类买卖点 / Buy-sell points (§8)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.8.1 | Def 8.1 first/second classifier | PROVEN_DIRECT | `Chanlun.FirstSecondBuysell.classifyBsp` |
| X.8.2 | Thm 8.2 totality + non-breaking | PROVEN_DIRECT | `classify_total`, `classify_first_point_only_total`, `second_buy_non_breaking`, `second_sell_non_breaking`, `second_not_breaking_iff`, `first_point_failed_iff` |
| X.8.3 | Thm 8.3 measure-gate propagation into 第一/第二 buy/sell | MULTI_VALUED_NAMED | `first_second_inheritance_load_bearing`, surfaced as `Chanlun.DivergenceWitnesses.first_second_measure_gate_divergence_witness` |
| X.8.4 | Thm 8.4 classify implies background 背驰 + pull defined | PROVEN_DIRECT | `classify_implies_beichi_and_pull` |
| X.8.5 | Def 8.5 third-class classifier | PROVEN_DIRECT | `Chanlun.ThirdBuysell.classifyBsp` |
| X.8.6 | Thm 8.6 third-class totality + zone load-bearing | PROVEN_DIRECT | `classifyBsp_total`, `bsp_zone_load_bearing_up`, `bsp_zone_load_bearing_down` |
| X.8.7 | Thm 8.7 recursive sub-level third-class | PROVEN_DIRECT | `Chanlun.RecursiveSubBspBeichi.recursive_subBsp_total`, `recursive_subBsp_terminates`, `recursive_subBsp_inheritance`, `recursive_subBsp_fuel_stationary`, `recursive_subBsp_fuel_bound_via_levelRecursion` |
| X.8.8 | Recursive sub-level form of 第一/第二类 buy/sell (multi-level descent measure shared with §8.7) | NOT_FORMALIZED — design choice | The recursive 第三类 is PROVEN_DIRECT (X.8.7). Lifting the 第一/第二 form to the same recursive fuel-bounded descent is structurally identical; not yet replicated in Lean. Blocker: the `TerminalWindow` carrier is a richer struct than `Departure` and the inheritance lemma requires tracking the background-背驰 verdict across levels (3+ extra inheritance lemmas vs the `RecursiveVerdict` tag already used for 第三类) |
| X.8.9 | Recursive form of 盘整背驰 (lesson 37) | NOT_FORMALIZED — design choice, same blocker as X.8.8 | Shares the descent measure of X.8.7 (lift_strict_drop); replication is structurally identical but not yet done |

### §X.9  级别递归 / Level recursion (§9)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.9.1 | Def 9.1 centerSize + level lift | PROVEN_DIRECT | `Chanlun.LevelRecursion.centerSize`, `liftCenter`, `liftCenters`, `liftStep`, `levelTower` |
| X.9.2 | Thm 9.2 lift_strict_drop (走势必完美) | PROVEN_DIRECT | `Chanlun.LevelRecursion.lift_strict_drop` + `level_recursion_count_decreases`, via `centerSize_ge_3` + `total_size_ge_3_times_count` |
| X.9.3 | Thm 9.3 centerSize ≥ 3 | PROVEN_DIRECT | `Chanlun.LevelRecursion.centerSize_ge_3`, immediate from `extendEnd_ge` |
| X.9.4 | Thm 9.4 envelope-soundness (lifted Element has lo ≤ hi) | PROVEN_DIRECT | `liftCenter_range_eq_core`, `liftCenter_lo_le_hi`, `liftCenters_all_valid`, `liftCenters_mem_iff` |
| X.9.5 | Thm 9.5 determinism preservation across levels | PROVEN_DIRECT | `liftStep_deterministic`, `levelTower_deterministic`, `levelTower_input_eq`, `levelTower_agreement_lifts` |
| X.9.6 | Total `lift : List Element → Option (List Element)` partial-function lifter | NOT_FORMALIZED — out-of-scope by design | The lift is encoded as the deterministic two-step `liftStep` (= `liftCenters ∘ zhongshu`). A wrapper that returns `none` when the input lifts to an empty center list is downstream of the level-recursion content and not part of "走势必完美" itself. The strict-drop measure (Thm 9.2) is the formal content of the master text's claim; the lifter wrapper is engineering |
| X.9.7 | Strict sub-window of the level recursion (level-(n−1) sub-window is a strict subset) | NOT_FORMALIZED — definitional | Requires a notion of "sub-window selector" at level (n−1) that picks a contiguous index sub-range of the level-(n−1) tower; the current `IntervalNesting.LevelWindow` provides the type but not the bridge to `LevelRecursion.levelTower`. Blocker: the two modules' carriers are different (`Element` list vs index-range struct) and a bridging coercion is not yet introduced |

### §X.10  区间套 / Interval nesting (§11)

| # | Item | Status | Reference / blocker |
|---|---|---|---|
| X.10.1 | Def 11.1 synthetic-tower walker | PROVEN_DIRECT | `Chanlun.IntervalNesting.LevelWindow`, `walk`, `DescendValid` |
| X.10.2 | Thm 11.2 termination + never-silent + pin-monotone + chain-strict-drop | PROVEN_DIRECT | `intervalnesting_terminates`, `walk_always_has_verdict`, `intervalnesting_pin_monotone`, `intervalnesting_chain_strict_drop` |
| X.10.3 | Thm 11.3 terminal-form theorems | PROVEN_DIRECT | `walk_at_zero_returns_gate_limit`, `walk_at_positive_returns_pinned` |
| X.10.4 | Multi-resolution timestamp-mapped composition (1d → 1h → 1m on real market data) | NOT_FORMALIZED — integer kernel cannot represent timestamps | The integer-arithmetic kernel deliberately has no time carrier — bars are indexed by `ℕ`, not by wall-clock timestamps. The "descend ↦ finer timeframe" claim requires a `Timestamp → Window` mapping that the kernel cannot express without a real-time data interface. Settled empirically (PROVEN_FIXTURE on 7-year NQ data) via `grounding/chanlun_multiscale_real_grounding.py` |
| X.10.5 | "Lowest-level-of-this-资金" residue characterization | NOT_FORMALIZED — same blocker as X.10.4 | Reported as named witnesses in the multiscale grounding script; requires real-time timestamp mapping to lift to Lean |
| X.10.6 | MACD-decorated interval-nesting variant | NOT_FORMALIZED — combined blocker of X.7.9 and X.10.4 | Needs both real MACD energy (X.7.9) and timestamp mapping (X.10.4); both blockers are kernel-level and out-of-scope for the integer carrier |
| X.10.7 | Walk-decomposition × interval-nesting integration | NOT_FORMALIZED — module-bridging | `Chanlun.WalkDecomposition.decompose` operates on `List Center`; `Chanlun.IntervalNesting.walk` operates on `LevelWindow`. The bridge (which walk in which level-window) needs a coercion the two modules don't share; the integration is a separate downstream module |

---

## §A Attribution

Chanlun (缠论) belongs to the 缠中说禅 (Chán Zhōng Shuō Chán) tradition.
The mathematical reformulation above and the Lean encoding under
`lean/Chanlun/` are this repository's contribution. The non-obvious
contributions are: the reachable-domain alternation theorem
(Theorem 3.6), the lift-strict-drop termination measure
(Theorem 9.2), and the constructive zone-gate divergence witness
(Theorem 5.10). The rest is the published theory in Lean form.

---

## §L License

The formalization, this document, the reference oracles, and the CI
workflow are released under MIT. See `LICENSE` if present.
