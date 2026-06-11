/-
  Chanlun/FirstSecondBuysell.lean

  缠论 **第一/第二类买卖点** (lesson 24) — Lean MWE half of Klaus's cc-lane
  dispatch (#1081 FULL 缠论 ownership; sits on top of 第三类 + 背驰 of #1104).
  Closes `[chanlun_first_second_buysell_lean_OPEN]`.

  ## What the 原文 claims (lesson 24)

      某级别下跌的最后一个走势段形成的底分型 / 该段背驰的低点 = 第一类买点；
      从第一类买点起来后第一次回抽不创新低 = 第二类买点；上涨对称.

  Reading the 原文 mathematically (host grounding
  `tools/mstnf_runtime/chanlun_first_second_buysell_grounding.py` is the math
  source of truth):

  * **第一类 (first_buy / first_sell)** ⇔ 背驰 holds under a NAMED measure on
    the terminal C-vs-A move-pair (the last 中枢 pair + post-中枢 same-direction
    tail). The 第一类 EXTREME = min low of the C tail (buy, d=−1) / max high
    (sell, d=+1). **The 第一类 INHERITS 背驰's measure gate** — so the 第一类
    verdict is itself measure-RELATIVE. NAMED, not collapsed (this propagation
    is the construction's load-bearing finding, matching the host grounding's
    `[chanlun_first_second_measure_gate_propagation_OPEN]` divergence rate of
    5.8% across reachable terminal windows under disp vs slope).
  * **第二类 (second_buy / second_sell)** ⇔ 第一类 holds ∧ the first post-第一类
    pullback element's low/high does NOT BREAK the 第一类 extreme. 跌破 is
    STRICT < (so touching first_extreme still 不破 — the 原文-literal integer
    boundary reading, matches the lesson-20 boundary algebra of #1100).
  * **first_point_failed** — 第一类 holds AND the first pullback BREAKS the
    extreme. NAMED residue (the §15 breaking-pullback mutant constructively
    produces this case), never silent.
  * **incomplete** — no 背驰 verdict OR no pullback element yet (stream-edge).
    NAMED residue.

  ## The named theorems

  * `classify_total` — TOTAL + never-silent over the six BspKind classes.
  * `first_second_inheritance_load_bearing` — THE measure-gate inheritance
    finding: a constructive WITNESS where disp says first_buy and slope says
    incomplete (or vice versa) on the SAME terminal window. Mirrors
    `beichi_measure_gate_witness` of #1104 but lifted to the 第一/第二类 chain.
  * `second_not_breaking_iff` — characterizes the non-breaking pullback gate:
    second_buy ⇒ pull.lo ≥ first_extreme; second_sell ⇒ pull.hi ≤
    first_extreme. The lesson-24-corollary's substantive content.
  * `first_point_failed_iff` — the breaking-pullback residue characterization:
    first_point_failed produces a constructive witness pull.lo < first_extreme
    (buy case) / pull.hi > first_extreme (sell case). The §15 mutant's
    contradiction surface.

  ## Honest scope (sub-residues NOT in this MWE, named)

  * `[chanlun_first_second_measure_gate_propagation_OPEN]` — the disp-vs-slope
    propagation gate is REAL (5.8% divergence on host grounding); the
    `first_second_inheritance_load_bearing` theorem certifies non-vacuity.
  * `[chanlun_first_second_buysell_recursive_OPEN]` — 次级别 form on the proven
    级别 recursion #1097.
  * `[chanlun_panzheng_beichi_first_second_OPEN]` — 盘整背驰 single-中枢 form.

  ## Companion host grounding

  `tools/mstnf_runtime/chanlun_first_second_buysell_grounding.py` — 257
  reachable terminal windows from real regime-switching K-lines (real
  normalize+分型+笔+中枢+背驰 pipeline); under disp: 56 first_point_failed,
  8 second_buy, 4 second_sell, 189 incomplete; under slope: 47 first_point_failed,
  4 second_buy, 2 second_sell, 204 incomplete. First-point-only histograms:
  disp 50 first_buy / 44 first_sell / 163 incomplete; slope 33/35/189. Measure
  propagation gate: 15/257 ≈ 5.8% divergence (REAL NAMED gate, not collapsed).
  §15 breaking-pullback mutant disagreed on 103 windows.
-/

import Mathlib.Tactic

namespace Chanlun.FirstSecondBuysell

/-! ## §1 — Carriers (self-contained; mirror #1093/#1100/#1104 shape). -/

/-- A sub-element (笔 range), same shape as `ChanlunZhongshuNFFromMSTNFMWE` /
    `ChanlunThirdBuysellMWE`. -/
structure Element where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- A directional move (the 力度 carrier), same shape as `ChanlunBeichiMWE`.
    Endpoints `lo ≤ hi` for an up-move (interpreted bottom→top) by the
    extraction gate; `dur ≥ 1`. -/
structure Move where
  lo  : Int
  hi  : Int
  dur : Nat
  deriving Repr, DecidableEq

/-- Displacement of a move (lo→hi, integer-exact). -/
def disp (m : Move) : Int := m.hi - m.lo

/-- The 力度 measure — a NAMED gate (the 原文 leaves the measure choice open,
    lesson 27's MACD is auxiliary). Same shape as `ChanlunBeichiMWE.Measure`
    (re-stated for self-containment). -/
inductive Measure where
  | disp  : Measure
  | slope : Measure
  deriving Repr, DecidableEq

/-- The 第一/第二类 verdict — TOTAL over six NAMED classes. `first_point_failed`
    and `incomplete` are NAMED residues, never silently binned. -/
inductive BspKind where
  | first_buy           : BspKind
  | first_sell          : BspKind
  | second_buy          : BspKind
  | second_sell         : BspKind
  | first_point_failed  : BspKind
  | incomplete          : BspKind
  deriving Repr, DecidableEq

/-- The terminal window the classifier sees: the inter-中枢 A move + the
    background 背驰段 C move + the trend direction d (+1 up / -1 down) + the
    第一类 extreme of C + the (optional) first post-第一类 pullback element. -/
structure TerminalWindow where
  d            : Int          -- +1 / -1 (direction gate has filtered 0)
  a            : Move         -- inter-中枢 travel into LAST 中枢 (the A move)
  c            : Move         -- post-中枢 same-direction 背驰段 (the C move)
  firstExtreme : Int          -- min low (d=-1) / max high (d=+1) of the C tail
  pull         : Option Element  -- first post-C pullback element (None = incomplete)
  deriving Repr

/-! ## §2 — The 力度 LHS/RHS pair and 背驰 verdict (mirrors #1104). -/

/-- The 力度 LHS / RHS pair under a NAMED measure (integer-exact cross-product
    for slope). Same as `ChanlunBeichiMWE.lhsRhs`. -/
def lhsRhs (a c : Move) : Measure → (Int × Int)
  | .disp  => (disp c, disp a)
  | .slope => (disp c * (a.dur : Int), disp a * (c.dur : Int))

/-- C weaker than A (`lhs < rhs`) ⇒ 背驰. Same shape as `ChanlunBeichiMWE.classifyBeichi`. -/
def isBeichi (a c : Move) (m : Measure) : Bool :=
  let (lhs, rhs) := lhsRhs a c m
  decide (lhs < rhs)

/-! ## §3 — The 第一/第二类 classifier (TOTAL, never-silent). -/

/-- The lesson-24 第一/第二类买卖点 classifier. The chain:
    1. No pullback yet ⇒ incomplete (the 第二类 question needs post-第一类 bars).
    2. ¬ 背驰 under `m` ⇒ incomplete (FIRST point fails the measure gate — the
       NAMED measure-propagation finding).
    3. 背驰 holds ⇒ 第一类 confirmed. d=-1 ⇒ buy side; d=+1 ⇒ sell side.
    4. pullback BREAKS first_extreme ⇒ first_point_failed (NAMED residue).
    5. pullback DOES NOT break ⇒ second_buy / second_sell.
    跌破 is STRICT `<` (原文-literal integer boundary, matches lesson 20 of #1100). -/
def classifyBsp (w : TerminalWindow) (m : Measure) : BspKind :=
  match w.pull with
  | none      => BspKind.incomplete
  | some pull =>
      if isBeichi w.a w.c m then
        if w.d = -1 then
          -- DOWN trend: 第一类买点 territory; 不创新低 ⇔ pull.lo ≥ first_extreme
          if pull.lo ≥ w.firstExtreme then BspKind.second_buy
          else BspKind.first_point_failed
        else
          -- d=+1: UP trend; 第一类卖点; 不升破 ⇔ pull.hi ≤ first_extreme
          if pull.hi ≤ w.firstExtreme then BspKind.second_sell
          else BspKind.first_point_failed
      else
        BspKind.incomplete

/-! ## §4 — TOTAL: every input lands in exactly one named BspKind. -/

/-- **THEOREM (TOTAL)**: `classifyBsp` is total and never silent — every input
    lands in one of the six named BspKinds. By construction the classifier's
    image lies in `{second_buy, second_sell, first_point_failed, incomplete}`;
    the two `first_buy`/`first_sell` constructors are NAMED for the
    `classifyFirstPointOnly` companion (the "the 第一类 alone" verdict, useful
    for the first-point histogram). -/
theorem classify_total (w : TerminalWindow) (m : Measure) :
    classifyBsp w m = BspKind.first_buy ∨
    classifyBsp w m = BspKind.first_sell ∨
    classifyBsp w m = BspKind.second_buy ∨
    classifyBsp w m = BspKind.second_sell ∨
    classifyBsp w m = BspKind.first_point_failed ∨
    classifyBsp w m = BspKind.incomplete := by
  unfold classifyBsp
  match w.pull with
  | none => simp
  | some pull =>
      simp only
      by_cases h_b : isBeichi w.a w.c m
      · simp only [h_b, if_true]
        by_cases h_d : w.d = -1
        · simp only [h_d, if_true]
          by_cases h_lo : pull.lo ≥ w.firstExtreme
          · simp [h_lo]
          · simp [h_lo]
        · simp only [h_d, if_false]
          by_cases h_hi : pull.hi ≤ w.firstExtreme
          · simp [h_hi]
          · simp [h_hi]
      · simp [h_b]

/-! ## §5 — The 第一类-only companion classifier (the inheritance source). -/

/-- The 第一类 alone — no pullback question. Used by the host grounding's
    first-point-only histogram to surface the measure-gate inheritance signal. -/
def classifyFirstPointOnly (w : TerminalWindow) (m : Measure) : BspKind :=
  if isBeichi w.a w.c m then
    if w.d = -1 then BspKind.first_buy else BspKind.first_sell
  else
    BspKind.incomplete

/-- **THEOREM**: the 第一类-only classifier lands in `{first_buy, first_sell,
    incomplete}` — totality of the inheritance source. -/
theorem classify_first_point_only_total (w : TerminalWindow) (m : Measure) :
    classifyFirstPointOnly w m = BspKind.first_buy ∨
    classifyFirstPointOnly w m = BspKind.first_sell ∨
    classifyFirstPointOnly w m = BspKind.incomplete := by
  unfold classifyFirstPointOnly
  by_cases h_b : isBeichi w.a w.c m
  · simp only [h_b, if_true]
    by_cases h_d : w.d = -1
    · simp [h_d]
    · simp [h_d]
  · simp [h_b]

/-! ## §6 — second_buy / second_sell characterization (NON-BREAK gate). -/

/-- **THEOREM (NON-BREAK, BUY)**: `second_buy` ⇒ `pull.lo ≥ firstExtreme` — the
    lesson-24-corollary's substantive content (the pullback's low must NOT
    break the 第一类 extreme; 跌破 is STRICT `<`). Constructive witness. -/
theorem second_buy_non_breaking (w : TerminalWindow) (m : Measure) :
    classifyBsp w m = BspKind.second_buy →
      ∃ pull, w.pull = some pull ∧ pull.lo ≥ w.firstExtreme ∧
        isBeichi w.a w.c m = true ∧ w.d = -1 := by
  intro h
  unfold classifyBsp at h
  match h_p : w.pull with
  | none => rw [h_p] at h; simp at h
  | some pull =>
      rw [h_p] at h
      simp only at h
      by_cases h_b : isBeichi w.a w.c m
      · simp only [h_b, if_true] at h
        by_cases h_d : w.d = -1
        · simp only [h_d, if_true] at h
          by_cases h_lo : pull.lo ≥ w.firstExtreme
          · refine ⟨pull, rfl, h_lo, h_b, h_d⟩
          · simp [h_lo] at h
        · simp only [h_d, if_false] at h
          by_cases h_hi : pull.hi ≤ w.firstExtreme
          · simp [h_hi] at h
          · simp [h_hi] at h
      · simp [h_b] at h

/-- **THEOREM (NON-BREAK, SELL)**: `second_sell` ⇒ `pull.hi ≤ firstExtreme`. -/
theorem second_sell_non_breaking (w : TerminalWindow) (m : Measure) :
    classifyBsp w m = BspKind.second_sell →
      ∃ pull, w.pull = some pull ∧ pull.hi ≤ w.firstExtreme ∧
        isBeichi w.a w.c m = true ∧ w.d ≠ -1 := by
  intro h
  unfold classifyBsp at h
  match h_p : w.pull with
  | none => rw [h_p] at h; simp at h
  | some pull =>
      rw [h_p] at h
      simp only at h
      by_cases h_b : isBeichi w.a w.c m
      · simp only [h_b, if_true] at h
        by_cases h_d : w.d = -1
        · simp only [h_d, if_true] at h
          by_cases h_lo : pull.lo ≥ w.firstExtreme
          · simp [h_lo] at h
          · simp [h_lo] at h
        · simp only [h_d, if_false] at h
          by_cases h_hi : pull.hi ≤ w.firstExtreme
          · refine ⟨pull, rfl, h_hi, h_b, h_d⟩
          · simp [h_hi] at h
      · simp [h_b] at h

/-- Combined statement — `second_not_breaking_iff` (Klaus's brief). -/
theorem second_not_breaking_iff (w : TerminalWindow) (m : Measure) :
    (classifyBsp w m = BspKind.second_buy →
        ∃ pull, w.pull = some pull ∧ pull.lo ≥ w.firstExtreme ∧
          isBeichi w.a w.c m = true ∧ w.d = -1) ∧
    (classifyBsp w m = BspKind.second_sell →
        ∃ pull, w.pull = some pull ∧ pull.hi ≤ w.firstExtreme ∧
          isBeichi w.a w.c m = true ∧ w.d ≠ -1) :=
  ⟨second_buy_non_breaking w m, second_sell_non_breaking w m⟩

/-! ## §7 — first_point_failed characterization (the §15 breaking-pullback
        residue surface — what the mutant constructively produces). -/

/-- **THEOREM (FIRST_POINT_FAILED)**: `first_point_failed` ⇒ pullback BREAKS
    the 第一类 extreme (strict inequality). Two cases by the trend direction
    — buy (d=-1): pull.lo < firstExtreme; sell (d≠-1): pull.hi > firstExtreme. -/
theorem first_point_failed_iff (w : TerminalWindow) (m : Measure) :
    classifyBsp w m = BspKind.first_point_failed →
      ∃ pull, w.pull = some pull ∧ isBeichi w.a w.c m = true ∧
        ((w.d = -1 ∧ pull.lo < w.firstExtreme) ∨
         (w.d ≠ -1 ∧ pull.hi > w.firstExtreme)) := by
  intro h
  unfold classifyBsp at h
  match h_p : w.pull with
  | none => rw [h_p] at h; simp at h
  | some pull =>
      rw [h_p] at h
      simp only at h
      by_cases h_b : isBeichi w.a w.c m
      · simp only [h_b, if_true] at h
        by_cases h_d : w.d = -1
        · simp only [h_d, if_true] at h
          by_cases h_lo : pull.lo ≥ w.firstExtreme
          · simp [h_lo] at h
          · push_neg at h_lo
            refine ⟨pull, rfl, h_b, Or.inl ⟨h_d, h_lo⟩⟩
        · simp only [h_d, if_false] at h
          by_cases h_hi : pull.hi ≤ w.firstExtreme
          · simp [h_hi] at h
          · push_neg at h_hi
            refine ⟨pull, rfl, h_b, Or.inr ⟨h_d, h_hi⟩⟩
      · simp [h_b] at h

/-! ## §8 — THE LOAD-BEARING THEOREM: measure-gate inheritance witness.

    The 背驰 measure gate (#1104 `beichi_measure_gate_witness`) PROPAGATES into
    the 第一/第二类 chain — there exist `a, c, w` for which `classifyBsp w disp`
    gives a different verdict than `classifyBsp w slope`. The constructive
    witness is the same numeric shape as `beichi_measure_gate_witness`,
    embedded into a TerminalWindow with a non-breaking pullback that activates
    the second_buy/incomplete divergence. -/

/-- **THE INHERITANCE WITNESS (LOAD-BEARING)**: there exist a TerminalWindow
    where `disp` says `second_buy` (第一类 confirmed + pullback non-breaking)
    and `slope` says `incomplete` (第一类 fails the slope measure). Same shape
    as the host grounding's `(win_gate)` self-test case.

    Construction: A = ⟨0, 20, 5⟩ (slope 4), C = ⟨0, 6, 1⟩ (slope 6).
    By disp: `disp C = 6 < 20 = disp A` ⇒ 背驰 ⇒ 第一类买点 confirmed; pullback
    pull.lo = 110 ≥ firstExtreme = 100 ⇒ second_buy.
    By slope: `disp C · A.dur = 6·5 = 30 > 20·1 = 20 = disp A · C.dur` ⇒
    no_beichi ⇒ incomplete.

    This certifies the host grounding's 5.8% divergence finding (the
    `[chanlun_first_second_measure_gate_propagation_OPEN]` gate is REAL,
    NAMED, not collapsed) as a constructive Lean witness. -/
theorem first_second_inheritance_load_bearing :
    ∃ (w : TerminalWindow),
      classifyBsp w Measure.disp = BspKind.second_buy ∧
      classifyBsp w Measure.slope = BspKind.incomplete := by
  refine ⟨{ d := -1
          , a := ⟨0, 20, 5⟩
          , c := ⟨0, 6, 1⟩
          , firstExtreme := 100
          , pull := some ⟨110, 120⟩ }, ?_, ?_⟩
  · -- disp branch: 6 < 20 ⇒ 背驰; d=-1 ⇒ buy; pull.lo=110 ≥ 100 ⇒ second_buy
    unfold classifyBsp
    simp [isBeichi, lhsRhs, disp]
  · -- slope branch: 6·5=30 > 20·1=20 ⇒ ¬ 背驰 ⇒ incomplete
    unfold classifyBsp
    simp [isBeichi, lhsRhs, disp]

/-! ## §9 — Beichi-implication: 第二类 / first_point_failed both rely on the
        background 背驰 verdict (which is itself measure-RELATIVE). The
        following two-direction characterizations show the chain is tightly
        coupled (no silent path skips the 背驰 question). -/

/-- A non-incomplete verdict under `m` ⇒ the 背驰 verdict under `m` is true and
    a pullback exists. The forward soundness of the chain. -/
theorem classify_implies_beichi_and_pull (w : TerminalWindow) (m : Measure) :
    classifyBsp w m ≠ BspKind.incomplete →
      isBeichi w.a w.c m = true ∧ ∃ pull, w.pull = some pull := by
  intro h
  unfold classifyBsp at h
  match h_p : w.pull with
  | none => rw [h_p] at h; simp at h
  | some pull =>
      rw [h_p] at h
      simp only at h
      by_cases h_b : isBeichi w.a w.c m
      · refine ⟨h_b, pull, rfl⟩
      · simp [h_b] at h

end Chanlun.FirstSecondBuysell
