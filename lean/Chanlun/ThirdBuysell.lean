/-
  Chanlun/ThirdBuysell.lean

  缠论 **第三类买卖点** (lesson 20) — Lean MWE half of Klaus's parallel-cc
  dispatch (#1081 09:01:36Z + 09:09:56Z, post-中枢 #1093 / 走势类型 #1095).
  Closes `[chanlun_third_buysell_lean_OPEN]`.

  ## What the 原文 claims (lesson 20, verbatim)

      一个次级别走势类型向上离开缠中说禅走势中枢，然后以一个次级别走势类型
      回试，其低点不跌破 ZG，则构成第三类买点；一个次级别走势类型向下离开
      缠中说禅走势中枢，然后以一个次级别走势类型回抽，其高点不升破 ZD，
      则构成第三类卖点.

  Reading the 原文 mathematically (host grounding
  `tools/mstnf_runtime/chanlun_third_buysell_grounding.py` is the math source
  of truth):

  * **三买 (third_buy)** ⇔ up-departure (`dep.lo > ZG`) ∧ pullback low not
    breaking ZG (`pull.lo ≥ ZG` — 跌破 is STRICT `<`, so touching ZG still
    qualifies; this is the 原文-literal integer boundary reading).
  * **三卖 (third_sell)** ⇔ down-departure (`dep.hi < ZD`) ∧ pullback high
    not breaking ZD (`pull.hi ≤ ZD`).
  * **reenter_up / reenter_down** — departure + pullback that re-enters the
    zone (`pull.lo < ZG` after up-departure / `pull.hi > ZD` after down).
    A NAMED residue (中枢 延伸/扩展 candidate), never a silent default.
  * **incomplete** — `dep` or `pull` not yet present (stream-edge 中枢).
  * **not_departed** — `dep` overlaps the zone (defensive carrier — the
    reachable host pipeline rules this out via the 中枢 termination
    condition, asserted as `bsp_reachable_no_not_departed` once we know
    departure entirely outside the zone).

  ## The named theorems (Klaus's brief, target shapes)

  ```
  inductive BspKind | third_buy | third_sell | reenter_up | reenter_down
                    | incomplete | not_departed
  structure Departure where
      center  : Center           -- the just-completed 中枢 [ZD, ZG]
      dep     : Option Element   -- the departure element (None ⇒ incomplete)
      pull    : Option Element   -- the pullback element  (None ⇒ incomplete)
  def classifyBsp : Departure → BspKind
  theorem classifyBsp_total
  theorem bsp_zone_load_bearing
  theorem bsp_excl
  ```

  ## Honest scope (sub-residues, NOT in this MWE)

  * `[chanlun_first_second_buysell_OPEN]` — 第一/第二类买卖点 (need 背驰).
  * `[chanlun_beichi_lean_OPEN]` — the 背驰 力度 measure (companion file
    `ChanlunBeichiMWE.lean`, this PR).
  * `[chanlun_third_buysell_recursive_OPEN]` — 次级别 走势 lift on the
    proven 级别 recursion.
  * `[chanlun_zhongshu_extension_OPEN]` — 中枢 延伸/扩展 vs 三买卖 disambig.

  ## Companion host grounding (Klaus arch-prep PR #1100 / commit 6e9d93db)

  `tools/mstnf_runtime/chanlun_third_buysell_grounding.py` — 1717 reachable
  windows (64 buy / 73 sell / 39 reenter / 1541 incomplete); §15 ZD-mutant
  disagreed on 24 windows — the ZG boundary IS the lesson-20 load-bearing
  content.
-/

import Mathlib.Tactic

namespace Chanlun.ThirdBuysell

/-! ## §1 — Carriers (re-stated for self-containment). -/

/-- A sub-element (笔 range), same shape as `ChanlunZhongshuNFFromMSTNFMWE`. -/
structure Element where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- A 中枢 carries its zone `[ZD, ZG]`. Re-stated from #1093 — only ZD/ZG
    are used by the classifier (start/end_ are inert here). -/
structure Center where
  start : Nat := 0
  end_  : Nat := 0
  ZD    : Int
  ZG    : Int
  deriving Repr, DecidableEq

/-- The 第三类买卖点 classification — TOTAL by construction. `reenter_*`,
    `incomplete`, `not_departed` are NAMED residues, never silent defaults. -/
inductive BspKind where
  | third_buy     : BspKind
  | third_sell    : BspKind
  | reenter_up    : BspKind
  | reenter_down  : BspKind
  | incomplete    : BspKind
  | not_departed  : BspKind
  deriving Repr, DecidableEq

/-- The post-中枢 window the classifier sees: the just-completed 中枢, plus
    optional departure / pullback elements (Option = stream-edge incomplete). -/
structure Departure where
  center : Center
  dep    : Option Element
  pull   : Option Element
  deriving Repr

/-! ## §2 — The classifier (lesson-20, integer boundary reading). -/

/-- The lesson-20 第三类买卖点 classifier. TOTAL + never-silent over
    `{third_buy, third_sell, reenter_up, reenter_down, incomplete,
    not_departed}`. The 原文-literal integer boundary: 跌破 ZG is STRICT
    `pull.lo < ZG`, so 不跌破 ⇔ `pull.lo ≥ ZG` (touching ZG still 三买). -/
def classifyBsp (d : Departure) : BspKind :=
  match d.dep, d.pull with
  | none, _ => BspKind.incomplete
  | _, none => BspKind.incomplete
  | some dep, some pull =>
      if dep.lo > d.center.ZG then
        -- 向上离开 (entirely above the zone)
        if pull.lo ≥ d.center.ZG then BspKind.third_buy else BspKind.reenter_up
      else if dep.hi < d.center.ZD then
        -- 向下离开 (entirely below the zone)
        if pull.hi ≤ d.center.ZD then BspKind.third_sell else BspKind.reenter_down
      else
        BspKind.not_departed

/-! ## §3 — TOTAL: every input lands in exactly one named BspKind. -/

/-- **THEOREM (TOTAL)**: `classifyBsp` is total and never silent — every
    input lands in one of the six named BspKinds. Trivial by case analysis. -/
theorem classifyBsp_total (d : Departure) :
    classifyBsp d = BspKind.third_buy ∨
    classifyBsp d = BspKind.third_sell ∨
    classifyBsp d = BspKind.reenter_up ∨
    classifyBsp d = BspKind.reenter_down ∨
    classifyBsp d = BspKind.incomplete ∨
    classifyBsp d = BspKind.not_departed := by
  unfold classifyBsp
  match h_dep : d.dep, h_pull : d.pull with
  | none, _ => simp
  | some _, none => simp
  | some dep, some pull =>
      simp only
      by_cases h_up : dep.lo > d.center.ZG
      · simp only [h_up, if_true]
        by_cases h_pull_ge : pull.lo ≥ d.center.ZG
        · simp [h_pull_ge]
        · simp [h_pull_ge]
      · simp only [h_up, if_false]
        by_cases h_dn : dep.hi < d.center.ZD
        · simp only [h_dn, if_true]
          by_cases h_pull_le : pull.hi ≤ d.center.ZD
          · simp [h_pull_le]
          · simp [h_pull_le]
        · simp [h_dn]

/-! ## §4 — The substantive theorem: lesson-20's ZG/ZD boundary is
        load-bearing (§15: the ZD-mutant disagrees on 24 host windows). -/

/-- **THE LOAD-BEARING THEOREM (UP)**: `third_buy` implies precisely
    lesson-20's 向上离开 + 不跌破 ZG geometry. -/
theorem bsp_zone_load_bearing_up (d : Departure) :
    classifyBsp d = BspKind.third_buy →
      ∃ dep pull, d.dep = some dep ∧ d.pull = some pull ∧
        dep.lo > d.center.ZG ∧ pull.lo ≥ d.center.ZG := by
  intro h
  unfold classifyBsp at h
  match h_dep : d.dep, h_pull : d.pull with
  | none, _ => rw [h_dep] at h; simp at h
  | some _, none => rw [h_dep, h_pull] at h; simp at h
  | some dep, some pull =>
      rw [h_dep, h_pull] at h
      simp only at h
      by_cases h_up : dep.lo > d.center.ZG
      · simp only [h_up, if_true] at h
        by_cases h_pull_ge : pull.lo ≥ d.center.ZG
        · refine ⟨dep, pull, rfl, rfl, h_up, h_pull_ge⟩
        · simp [h_pull_ge] at h
      · simp only [h_up, if_false] at h
        by_cases h_dn : dep.hi < d.center.ZD
        · simp only [h_dn, if_true] at h
          by_cases h_pull_le : pull.hi ≤ d.center.ZD
          · simp [h_pull_le] at h
          · simp [h_pull_le] at h
        · simp [h_dn] at h

/-- **THE LOAD-BEARING THEOREM (DOWN)**: `third_sell` implies precisely
    lesson-20's 向下离开 + 不升破 ZD geometry. -/
theorem bsp_zone_load_bearing_down (d : Departure) :
    classifyBsp d = BspKind.third_sell →
      ∃ dep pull, d.dep = some dep ∧ d.pull = some pull ∧
        dep.hi < d.center.ZD ∧ pull.hi ≤ d.center.ZD := by
  intro h
  unfold classifyBsp at h
  match h_dep : d.dep, h_pull : d.pull with
  | none, _ => rw [h_dep] at h; simp at h
  | some _, none => rw [h_dep, h_pull] at h; simp at h
  | some dep, some pull =>
      rw [h_dep, h_pull] at h
      simp only at h
      by_cases h_up : dep.lo > d.center.ZG
      · simp only [h_up, if_true] at h
        by_cases h_pull_ge : pull.lo ≥ d.center.ZG
        · simp [h_pull_ge] at h
        · simp [h_pull_ge] at h
      · simp only [h_up, if_false] at h
        by_cases h_dn : dep.hi < d.center.ZD
        · simp only [h_dn, if_true] at h
          by_cases h_pull_le : pull.hi ≤ d.center.ZD
          · refine ⟨dep, pull, rfl, rfl, h_dn, h_pull_le⟩
          · simp [h_pull_le] at h
        · simp [h_dn] at h

/-- Combined statement matching Klaus's brief verbatim — `bsp_zone_load_bearing`. -/
theorem bsp_zone_load_bearing (d : Departure) :
    (classifyBsp d = BspKind.third_buy →
        ∃ dep pull, d.dep = some dep ∧ d.pull = some pull ∧
          dep.lo > d.center.ZG ∧ pull.lo ≥ d.center.ZG) ∧
    (classifyBsp d = BspKind.third_sell →
        ∃ dep pull, d.dep = some dep ∧ d.pull = some pull ∧
          dep.hi < d.center.ZD ∧ pull.hi ≤ d.center.ZD) :=
  ⟨bsp_zone_load_bearing_up d, bsp_zone_load_bearing_down d⟩

/-! ## §5 — EXCL: third_buy and third_sell are mutually exclusive on any
        nonempty zone (departure cannot be entirely above AND entirely
        below a `ZD ≤ ZG` zone simultaneously). -/

/-- **THEOREM (EXCL)**: third_buy and third_sell are mutually exclusive. By
    the up/down departure discriminator (`dep.lo > ZG` xor `dep.hi < ZD`
    over `ZD ≤ ZG`) — direct consequence of `classifyBsp`'s case split. -/
theorem bsp_excl (d : Departure) :
    classifyBsp d = BspKind.third_buy → classifyBsp d ≠ BspKind.third_sell := by
  intro h_buy h_sell
  -- A single classifyBsp value cannot be both .third_buy and .third_sell.
  rw [h_buy] at h_sell
  exact BspKind.noConfusion h_sell

/-- Symmetric: third_sell precludes third_buy. -/
theorem bsp_excl_sell (d : Departure) :
    classifyBsp d = BspKind.third_sell → classifyBsp d ≠ BspKind.third_buy := by
  intro h_sell h_buy
  rw [h_sell] at h_buy
  exact BspKind.noConfusion h_buy

/-! ## §6 — REENTER is the NAMED zone-re-entering residue (§15: the
        ZD-mutant of the grounding mistakes this for a 三买). -/

/-- **THEOREM (REENTER_UP)**: `reenter_up` characterizes precisely the
    up-departure + pullback-low-below-ZG case (the 中枢 延伸 candidate the
    §15 ZD-mutant silently mis-classifies as 三买). -/
theorem bsp_reenter_up_iff (d : Departure) :
    classifyBsp d = BspKind.reenter_up →
      ∃ dep pull, d.dep = some dep ∧ d.pull = some pull ∧
        dep.lo > d.center.ZG ∧ pull.lo < d.center.ZG := by
  intro h
  unfold classifyBsp at h
  match h_dep : d.dep, h_pull : d.pull with
  | none, _ => rw [h_dep] at h; simp at h
  | some _, none => rw [h_dep, h_pull] at h; simp at h
  | some dep, some pull =>
      rw [h_dep, h_pull] at h
      simp only at h
      by_cases h_up : dep.lo > d.center.ZG
      · simp only [h_up, if_true] at h
        by_cases h_pull_ge : pull.lo ≥ d.center.ZG
        · simp [h_pull_ge] at h
        · simp [h_pull_ge] at h
          refine ⟨dep, pull, rfl, rfl, h_up, ?_⟩
          omega
      · simp only [h_up, if_false] at h
        by_cases h_dn : dep.hi < d.center.ZD
        · simp only [h_dn, if_true] at h
          by_cases h_pull_le : pull.hi ≤ d.center.ZD
          · simp [h_pull_le] at h
          · simp [h_pull_le] at h
        · simp [h_dn] at h

/-- **THEOREM (REENTER_DOWN)** (symmetric). -/
theorem bsp_reenter_down_iff (d : Departure) :
    classifyBsp d = BspKind.reenter_down →
      ∃ dep pull, d.dep = some dep ∧ d.pull = some pull ∧
        dep.hi < d.center.ZD ∧ pull.hi > d.center.ZD := by
  intro h
  unfold classifyBsp at h
  match h_dep : d.dep, h_pull : d.pull with
  | none, _ => rw [h_dep] at h; simp at h
  | some _, none => rw [h_dep, h_pull] at h; simp at h
  | some dep, some pull =>
      rw [h_dep, h_pull] at h
      simp only at h
      by_cases h_up : dep.lo > d.center.ZG
      · simp only [h_up, if_true] at h
        by_cases h_pull_ge : pull.lo ≥ d.center.ZG
        · simp [h_pull_ge] at h
        · simp [h_pull_ge] at h
      · simp only [h_up, if_false] at h
        by_cases h_dn : dep.hi < d.center.ZD
        · simp only [h_dn, if_true] at h
          by_cases h_pull_le : pull.hi ≤ d.center.ZD
          · simp [h_pull_le] at h
          · simp [h_pull_le] at h
            refine ⟨dep, pull, rfl, rfl, h_dn, ?_⟩
            omega
        · simp [h_dn] at h

end Chanlun.ThirdBuysell
