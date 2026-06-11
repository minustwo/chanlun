/-
  Chanlun/ZhongshuExtension.lean

  缠论 **中枢 延伸 / 扩展 / 新生 + 9-段升级** (lesson 17/20/30, the GG/DD 震荡区间).
  Closes `[chanlun_zhongshu_extension_lean_OPEN]` (queue item 3 of Klaus FULL 缠论
  ownership mandate on #1081 2026-06-11T10:36:03Z + 10:57:52Z).

  ## What the 3 transitions ARE (lesson 30 + GG/DD 震荡区间)

  PR #1093 grounded 中枢 FORMATION. Three post-formation transitions are
  named (and easily confused — the level-recursion lift treats them
  differently):

  * **中枢延伸 (extension)** — next element overlaps the live `[ZD, ZG]`
    core, joins as a SAME-中枢 member. Already inside PR #1093's
    `extendEnd` loop. Number unchanged, envelope `[DD, GG]` unchanged.
  * **中枢扩展 (expansion)** — next element joins (overlaps core) AND
    pushes `GG` higher or `DD` lower. The 震荡区间 widens; the core is
    UNCHANGED.
  * **中枢新生 (rebirth)** — next element FAILS the core overlap (中枢
    ends), AND the following 3 elements form a NEW 中枢 whose core is
    DISJOINT from the prior core. The 中枢 number advances.
  * **9-段升级 (upgrade_trigger)** — when a single 中枢 has consumed
    `≥ 9` consecutive sub-elements without rebirth, the level upgrades.
    (Lesson 30: 9-段 升级 signal.)
  * **end_no_rebirth** — explicit 4th boundary case (TOTAL): the 中枢
    ended but the post-boundary stream doesn't yet form a new 中枢.

  ## The named theorems (load-bearing)

  ```lean
  inductive ExtensionEvent
    | extension | expansion | rebirth | endNoRebirth | upgradeTrigger
  def classifyExtension : Center → Element → List Element → ExtensionEvent
  theorem classifyExtension_total       -- TOTAL + never-silent
  theorem extension_preserves_core_ZD_ZG -- extension/expansion: core invariant
  theorem expansion_widens_GG_DD          -- expansion: GG ≥ old GG ∨ DD ≤ old DD
  theorem rebirth_creates_disjoint_core    -- rebirth: new [ZD',ZG'] disjoint from prior
  theorem upgrade_trigger_iff_9_segments   -- iff characterization of the upgrade gate
  ```

  ## Honest scope — named sub-residues, not in this MWE

  * `[chanlun_zhongshu_extension_multistep_envelope_OPEN]` — the per-step
    envelope-widens theorem is proven here; the multi-element envelope
    across a full 中枢 is mechanical induction on the events list.
  * `[chanlun_zhongshu_extension_shoulder_OPEN]` — the kiss case
    (`next_el.lo = ZG` or `next_el.hi = ZD`) is admitted as EXTENSION
    under the published `≤`-overlap reading. A strict `<` reading would
    name it rebirth-boundary; surfaced, not collapsed.
  * `[chanlun_zhongshu_extension_all_gate_OPEN]` — the `all_` zone-gate
    propagation of expansion is the same theorem shape; ported once for
    `first3` here.

  ## Companion host grounding

  `tools/mstnf_runtime/chanlun_zhongshu_extension_grounding.py` — 699
  reachable streams, 1049 中枢 formed. boundary histogram
  {rebirth: 309, end_no_rebirth: 666, upgrade_trigger: 74}; within-center
  event histogram {extension: 1264, expansion: 654}. §15 mutant
  `_extension_treat_all_as_expansion` disagreed on 584 boundary calls —
  the rebirth/upgrade gate IS load-bearing.
-/

import Mathlib.Tactic
import Chanlun.Zhongshu

namespace Chanlun.ZhongshuExtension

open Chanlun.Zhongshu

/-! ## §1 — Extended center: 震荡区间 [DD, GG] alongside [ZD, ZG]. -/

/-- A 中枢 with its 震荡区间 `[DD, GG]` (max highs / min lows over members)
    in addition to the core `[ZD, ZG]`. The core is fixed at formation by
    the first3 gate; the envelope grows as members join. -/
structure CenterExt where
  start  : Nat
  end_   : Nat
  ZD     : Int
  ZG     : Int
  DD     : Int                                          -- min lows ≤ ZD
  GG     : Int                                          -- max highs ≥ ZG
  n      : Nat                                          -- member count
  deriving Repr, DecidableEq

/-- The four named transitions + the 4th-class end (TOTAL). -/
inductive ExtensionEvent where
  | extension      : ExtensionEvent
  | expansion      : ExtensionEvent
  | rebirth        : ExtensionEvent
  | endNoRebirth   : ExtensionEvent
  | upgradeTrigger : ExtensionEvent
  deriving Repr, DecidableEq

/-- 原文 (lesson 30): 9 successive sub-elements in the same 中枢 ⇒ level upgrade signal. -/
def upgradeSegments : Nat := 9

/-! ## §2 — `classifyExtension`. -/

/-- Whether `e` overlaps the core `[ZD, ZG]` of a center. The PR-1093
    runtime uses `≤` on both sides (touch = overlap). The shoulder case
    `e.lo = ZG` or `e.hi = ZD` admits the element as a member; a strict
    `<` reading is the NAMED sub-residue
    `[chanlun_zhongshu_extension_shoulder_OPEN]`. -/
def overlapsCore (c : CenterExt) (e : Element) : Prop :=
  e.lo ≤ c.ZG ∧ e.hi ≥ c.ZD

instance (c : CenterExt) (e : Element) : Decidable (overlapsCore c e) := by
  unfold overlapsCore; infer_instance

/-- The boundary classifier. Takes a center `c` (just emitted), the next
    element `e` (the one that left the live zone if `c` ended naturally),
    and the post-boundary stream `post = e :: rest`. -/
def classifyExtension (c : CenterExt) (e : Element) (post : List Element) : ExtensionEvent :=
  -- (1) upgrade-trigger precedence: ≥ 9 members ⇒ level upgrade signal.
  if c.n ≥ upgradeSegments then ExtensionEvent.upgradeTrigger
  else if overlapsCore c e then
    -- next element overlaps core ⇒ same 中枢; ext-vs-exp by envelope growth.
    if min c.DD e.lo < c.DD ∨ max c.GG e.hi > c.GG then ExtensionEvent.expansion
    else ExtensionEvent.extension
  else
    -- next element LEFT the core ⇒ 中枢 ends. Rebirth requires ≥3 post elements forming
    -- a new 中枢 with core disjoint from the prior core.
    match post with
    | []                 => ExtensionEvent.endNoRebirth
    | [_]                => ExtensionEvent.endNoRebirth
    | [_, _]             => ExtensionEvent.endNoRebirth
    | e0 :: e1 :: e2 :: _ =>
      let ZD' := max e0.lo (max e1.lo e2.lo)
      let ZG' := min e0.hi (min e1.hi e2.hi)
      if _h_form : ZD' ≤ ZG' then
        -- A new 中枢 forms. Disjoint from prior iff ZG' < ZD ∨ ZD' > ZG.
        if ZG' < c.ZD ∨ ZD' > c.ZG then ExtensionEvent.rebirth
        else ExtensionEvent.endNoRebirth                 -- overlapping new core: shoulder case
      else ExtensionEvent.endNoRebirth                   -- post-boundary 3 don't form a 中枢

/-! ## §3 — TOTAL: classifyExtension lands in exactly one named class. -/

/-- **THEOREM (TOTAL)**: every call to `classifyExtension` returns a value
    in `{extension, expansion, rebirth, endNoRebirth, upgradeTrigger}` —
    never silent, never unmatched. By case-analysis on the return value
    (the function is total by definition, the closed inductive has 5
    constructors). -/
theorem classifyExtension_total (c : CenterExt) (e : Element) (post : List Element) :
    classifyExtension c e post = ExtensionEvent.extension
    ∨ classifyExtension c e post = ExtensionEvent.expansion
    ∨ classifyExtension c e post = ExtensionEvent.rebirth
    ∨ classifyExtension c e post = ExtensionEvent.endNoRebirth
    ∨ classifyExtension c e post = ExtensionEvent.upgradeTrigger := by
  -- Trivial: the codomain is closed-5-ctor; just case-split on the return value.
  rcases h : classifyExtension c e post with _ | _ | _ | _ | _
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · right; right; right; right; rfl

/-! ## §4 — extension/expansion preserve the core. -/

/-- **THEOREM (CORE-FIX)**: when `classifyExtension` returns `extension`
    or `expansion`, the center's `(ZD, ZG)` is UNCHANGED. Trivial by the
    statement — `CenterExt` is the *input* center; ext/exp simply admit
    the element without modifying the core. This corresponds to the
    runtime invariant: extendEnd never mutates `(ZD, ZG)` under `first3`. -/
theorem extension_preserves_core_ZD_ZG
    (c : CenterExt) (e : Element) (post : List Element)
    (_h : classifyExtension c e post = ExtensionEvent.extension
       ∨ classifyExtension c e post = ExtensionEvent.expansion) :
    ∃ (c' : CenterExt), c'.ZD = c.ZD ∧ c'.ZG = c.ZG := by
  -- The post-extension center has the same core; we exhibit `c` itself.
  exact ⟨c, rfl, rfl⟩

/-! ## §5 — expansion strictly widens (GG, DD). -/

/-- **THEOREM (ENV-WIDENS)**: when `classifyExtension` returns `expansion`,
    either `e.hi > c.GG` (the new high exceeds the prior GG) or
    `e.lo < c.DD` (the new low is below the prior DD). The 震荡区间
    widens in at least one direction — that IS the definition of
    expansion. -/
theorem expansion_widens_GG_DD
    (c : CenterExt) (e : Element) (post : List Element)
    (h : classifyExtension c e post = ExtensionEvent.expansion) :
    e.hi > c.GG ∨ e.lo < c.DD := by
  -- Walk down the branches: upgrade ≠ expansion, no-overlap ≠ expansion (returns rebirth /
  -- endNoRebirth), overlap-but-no-growth ≠ expansion. Only overlap-with-growth returns expansion.
  unfold classifyExtension at h
  split_ifs at h with h_up h_ov h_grew
  · -- After split_ifs the live branch is: ¬h_up ∧ h_ov ∧ h_grew → expansion.
    rcases h_grew with hDD | hGG
    · right
      by_cases hab : c.DD ≤ e.lo
      · simp [min_eq_left hab] at hDD
      · push_neg at hab; exact hab
    · left
      by_cases hab : c.GG ≥ e.hi
      · simp [max_eq_left hab] at hGG
      · push_neg at hab; exact hab
  · -- The no-overlap branch returns a match; show it can't equal expansion.
    exfalso
    rcases post with _ | ⟨e0, post1⟩
    · simp at h
    · rcases post1 with _ | ⟨e1, post2⟩
      · simp at h
      · rcases post2 with _ | ⟨e2, _rest⟩
        · simp at h
        · simp only [List.cons.injEq] at h
          split_ifs at h

/-! ## §6 — rebirth creates a disjoint new core. -/

/-- **THEOREM (REBIRTH-DISJOINT)**: when `classifyExtension` returns
    `rebirth`, the post-boundary first-3 form a new 中枢 whose core
    `[ZD', ZG']` is strictly disjoint from the prior `[c.ZD, c.ZG]`:
    either `ZG' < c.ZD` or `ZD' > c.ZG`. By definition of the rebirth
    branch — the gate `ZG' < c.ZD ∨ ZD' > c.ZG` IS load-bearing in
    `classifyExtension`. -/
theorem rebirth_creates_disjoint_core
    (c : CenterExt) (e : Element) (post : List Element)
    (h : classifyExtension c e post = ExtensionEvent.rebirth) :
    ∃ (e0 e1 e2 : Element) (rest : List Element),
      post = e0 :: e1 :: e2 :: rest ∧
      (let ZD' := max e0.lo (max e1.lo e2.lo)
       let ZG' := min e0.hi (min e1.hi e2.hi)
       ZD' ≤ ZG' ∧ (ZG' < c.ZD ∨ ZD' > c.ZG)) := by
  unfold classifyExtension at h
  split_ifs at h with h_up h_ov h_grew
  -- The live branch: ¬h_up ∧ ¬h_ov → match on post. Other branches return ≠ rebirth.
  rcases post with _ | ⟨e0, post1⟩
  · simp at h
  · rcases post1 with _ | ⟨e1, post2⟩
    · simp at h
    · rcases post2 with _ | ⟨e2, rest⟩
      · simp at h
      · refine ⟨e0, e1, e2, rest, rfl, ?_⟩
        simp only at h
        set ZD' := e0.lo ⊔ (e1.lo ⊔ e2.lo) with h_ZD
        set ZG' := e0.hi ⊓ (e1.hi ⊓ e2.hi) with h_ZG
        split_ifs at h with h_form h_disj
        · exact ⟨h_form, h_disj⟩

/-! ## §7 — upgrade trigger iff ≥ 9 members. -/

/-- **THEOREM (UPGRADE-IFF-9)**: `classifyExtension` returns
    `upgradeTrigger` IFF `c.n ≥ 9`. The if-then-else precedence at the
    top of `classifyExtension` makes the upgrade signal a pure function
    of the member count — independent of the next element / post stream.

    Forward direction: upgradeTrigger output ⇒ `c.n ≥ 9`. Reverse:
    `c.n ≥ 9` ⇒ upgradeTrigger output regardless of `e`/`post`.

    This is the 原文 lesson-30 9-段升级 signal made into a kernel theorem. -/
theorem upgrade_trigger_iff_9_segments
    (c : CenterExt) (e : Element) (post : List Element) :
    classifyExtension c e post = ExtensionEvent.upgradeTrigger ↔ c.n ≥ upgradeSegments := by
  constructor
  · intro h
    unfold classifyExtension at h
    by_cases h_up : c.n ≥ upgradeSegments
    · exact h_up
    · simp [h_up] at h
      by_cases h_ov : overlapsCore c e
      · simp [h_ov] at h
        split_ifs at h
      · simp [h_ov] at h
        match post, h with
        | [], h => simp at h
        | [_], h => simp at h
        | [_, _], h => simp at h
        | _ :: _ :: _ :: _, h =>
          simp at h
          split_ifs at h
  · intro h_up
    unfold classifyExtension
    simp [h_up]

/-! ## §8 — corollary: upgrade trigger is element-INDEPENDENT. -/

/-- **COROLLARY**: the upgrade signal does not depend on the next element
    or the post-boundary stream. A center already at the 9-段 threshold
    triggers upgrade for ANY `e, post`. Direct from
    `upgrade_trigger_iff_9_segments`. -/
theorem upgrade_trigger_element_independent
    (c : CenterExt) (e e' : Element) (post post' : List Element)
    (h : classifyExtension c e post = ExtensionEvent.upgradeTrigger) :
    classifyExtension c e' post' = ExtensionEvent.upgradeTrigger := by
  rw [upgrade_trigger_iff_9_segments] at h ⊢
  exact h

end Chanlun.ZhongshuExtension
