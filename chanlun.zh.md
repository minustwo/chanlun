# 缠论 —— 数学形式化

> 缠论的数学形态。下列每条定义和定理都在 `lean/Chanlun/` 中证明，无任何
> `sorry`。本文档是给人看的叙述形式；可信的承诺在 Lean 模块里。
>
> English version: [chanlun.md](chanlun.md).

---

## §0 记号

所有算术均在 `ℤ`（整数）上进行，`ℕ` 用作索引。形式系统**无浮点依赖**；
价格按整数标度输入（例如 CME 小型期货 0.25 跳点 ⇒ 价格 × 4）。这一整数
纪律让每条定理可判定、内核证明构造性。

* `Bar := { h : ℤ, l : ℤ }` —— K 线：高、低。
* `Interval := { l : ℤ, h : ℤ }` —— 同样的数据，字段顺序不同（包含处理
  算法使用；通过 `toBar : Interval → Bar` 桥接）。
* `Fractal := { idx : ℕ, kind : FractalKind, h : ℤ, l : ℤ }`，
  其中 `FractalKind ∈ { top, bottom, neither }`。
* `Stroke := { from_idx : ℕ, to_idx : ℕ, dir : StrokeDir }`，
  其中 `StrokeDir ∈ { up, down }`。
* `Center := { start : ℕ, end_ : ℕ, ZD : ℤ, ZG : ℤ }`（中枢）。

---

## §1 定义 3 —— 分型

### 顶分型

3 K 线窗口 `(a, b, c)` 是**顶分型** iff

```
b.h > a.h  ∧  b.h > c.h  ∧  b.l > a.l  ∧  b.l > c.l.
```

### 底分型

`(a, b, c)` 是**底分型** iff

```
b.h < a.h  ∧  b.h < c.h  ∧  b.l < a.l  ∧  b.l < c.l.
```

### 分类

```
classifyDef3(a, b, c) := if isTopFractal then top
                        else if isBottomFractal then bottom
                        else neither
```

### 定理 1.1（`def3_trichotomy`）

对每个 3 K 线窗口，`classifyDef3` 返回 `{top, bottom, neither}` 中恰好
一个，且 top/bottom 互斥（不存在同时满足的窗口）。

### 定理 1.2（`fractal_slot_equiv_def3`）

算子端整数编码分类器（`0 = top`、`1 = bottom`、`2 = neither`）等于
`kindToInt ∘ classifyDef3`，对每个窗口成立。

Lean 模块：[`Chanlun.Fractal`](lean/Chanlun/Fractal.lean)。

---

## §2 算法 N —— 包含处理（附录 A）

### 包含

相邻区间 `(a, b)` 处于**包含关系** iff
`(b.l ≤ a.l ∧ a.h ≤ b.h) ∨ (a.l ≤ b.l ∧ b.h ≤ a.h)`。

### `noAdjContainment`

区间列表 `noAdjContainment` iff 相邻对均不在包含关系中。

### 单次扫描 `normalize`

用方向感知的 `pushOne` 步骤走列表：

* 同方向 + 新 K 线被栈顶包含：用 `[max, max]`（上）/ `[min, min]`（下）
  合并；
* 否则 push。

### 定理 2.1（`normalize_no_adjacent_containment`）

对每个输入 `xs`，`noAdjContainment (normalize xs).1`。

等价地：单次从左到右扫描 + 方向合并已经生成了无包含商 —— 不需要第二
次扫描。

Lean 模块：[`Chanlun.Normalize`](lean/Chanlun/Normalize.lean)。

---

## §3 流水线组合（N → Def-3）

### `isInclusionNormalized`

3 K 线窗口 `(a, b, c)` 称为*包含归一* iff 相邻间均不存在彼此包含关系。

### 定理 3.1（`pipeline_inclusion_normalized`）

```
∀ xs, ∀ a b c rest,
  (normalize xs).1 = a :: b :: c :: rest →
  isInclusionNormalized (toBar b) (toBar a) (toBar c).
```

### 定理 3.2（`pipeline_fractal_classification_well_defined`）

经算法 N 后，结果栈中每个内部 3 K 线窗口均确定地分类为
`{top, bottom, neither}` 之一。

Lean 模块：[`Chanlun.Pipeline`](lean/Chanlun/Pipeline.lean)。

---

## §4 定义 4 —— 笔

### 构造（最左贪心）

用一个交替锚点走分型列表：

* 尚无锚点 → 把锚点设为当前分型 `f`；
* 同向分型 → 保留极值代表（`pickRep`）；
* 反向分型，间隔 `≥ δmin` → **发射**笔 `(锚点 → f)`，重锚到 `f`；
* 反向分型，间隔 `< δmin` → 丢弃（见 [`README.zh.md`](README.zh.md)
  的「已知限制」）。

### 定理 4.1（`stroke_emits_separated`，性质 B）

每条发射的笔满足 `δmin ≤ to_idx − from_idx`。

### 定理 4.2（`stroke_emits_alternate`，性质 A）

折叠内输出中相邻笔的方向相反。

### 定理 4.3（`strokes_separated`）

通过 `List.mem_reverse`，用户面向的反转输出笔列表继承间隔性质。

Lean 模块：[`Chanlun.Stroke`](lean/Chanlun/Stroke.lean)。

---

## §5 引理 2（强形式） —— 笔唯一性

### 结构有效性谓词 `IsValidBi`

参数为 `(Option Fractal × List Fractal × ℤ × List Stroke)` 的递归
谓词，与 `step` 的 case 分析一一对应。捕获：*from 端点是同向 run 的
极值代表；to 端点是锚点之后最左的反向 admissible 分型*。

### 定理 5.1（`strokes_unique`）

```
∀ frs δmin alt, IsValidBi frs δmin alt → alt = strokes frs δmin.
```

任何结构上有效的笔分解都等于流式规范输出。证明走广义化的
fold-vs-alt 不变量 `fold_consumes_alt`，沿 `frs` 归纳。

Lean 模块：[`Chanlun.StrokeUniqueness`](lean/Chanlun/StrokeUniqueness.lean)。

---

## §6 定义 5–16 + 定理 1 —— 线段

### BoundedFix 递归

`segments : (find_term : ℕ → Option ℕ) → (find_term_ge : property) → ℕ → ℕ → List Segment`。

参数化于一个 *最左 ≥ a* 的预言 `find_term` 及其契约
`find_term_ge : ∀ a j, find_term a = some j → a ≤ j`。完整的特征序列 Φ
+ 重叠 admissibility 内部细节在此未重新推导（见 `README.zh.md` 的
「已知限制」）；Lean 递归只需契约 `find_term_ge`。

### 定理 6.1（`segments_partition`，性质 P）

发射的线段是 `[a, n)` 的连续分划。

### 定理 6.2（`segments_terminate`，性质 T）

最多发射 `n - a + 1` 个线段（well-founded、有限列表）。

### 定理 6.3（`segment_advance_strictly_increasing`）

中心终止引理：
`find_term a = some j → a ≤ j → n - (j + 1) < n - a`。
`n − a` 测度严格下降 ⇒ BoundedFix 是良基的。

Lean 模块：[`Chanlun.Segment`](lean/Chanlun/Segment.lean)。

---

## §7 中枢（17/20 课）

### 构造

对 ℕ 索引的元素序列 `[lo, hi]`：

* 从 `i = 0` 开始扫描；
* 若 `els.length ≤ i + 2` → 停止;
* 令 `ZD := max(els[i].lo, els[i+1].lo, els[i+2].lo)` 和
  `ZG := min(els[i].hi, els[i+1].hi, els[i+2].hi)`；
* 若 `ZD ≤ ZG`（真重叠） → 发射中枢 `⟨i, extendEnd(i+3), ZD, ZG⟩`，
  从 `extendEnd + 1` 续；
* 否则 → 滑动 `i := i + 1`。

扩展函数 `extendEnd els g zd zg j` 在 `els[j]` 重叠在线 zone 时向前
走 `j`。参数 `g : ZoneGate ∈ {first3, all_}` 控制再收紧：

* `first3` 保持 `(zd, zg)` 不变；
* `all_` 收紧为 `(max zd els[j].lo, min zg els[j].hi)`。

缠论原文对此选择未明确，我们提供两种读法并证明两者均有效（见
`README.zh.md` 的「已知限制」）。

### 定理 7.1（`zhongshu_valid`）

对 `zhongshu` 产生的每个中枢 `c`，`c.ZD ≤ c.ZG`。由构造的成型 gate
直接保证。

### 定理 7.2（`zhongshu_disjoint`）

相邻中枢 `c₁ :: c₂ :: rest` 满足 `c₁.end_ < c₂.start`。

### 定理 7.3（`extendEnd_ge`）

`j - 1 ≤ extendEnd els g zd zg j`。中心终止引理，赋予 `zhongshu` 在
`els.length − i` 测度上的良基终止。

Lean 模块：[`Chanlun.Zhongshu`](lean/Chanlun/Zhongshu.lean)。

---

## §8 走势类型（17 课）

### 分类

```
classify : List Center → WalkType
classify []           = none_
classify [_]          = consolidation
classify (c₁::c₂::rs) = if allUp then trend_up
                      else if allDown then trend_down
                      else mixed
```

`allUp` / `allDown` 是相邻 `stepDir` 函数（`up` iff 下个中枢
`ZD > 前一个 ZG`；`down` iff 下个 `ZG < 前一个 ZD`；否则 `neither`）的
可判定谓词。

### 定理 8.1（`classify_total`）

`classify cs` 对每个 `cs` 都是
`{none_, consolidation, trend_up, trend_down, mixed}` 之一。Total +
绝不静默。

### 定理 8.2（`classify_trend_monotone`）

```
(classify cs = trend_up   → allStepsAreUp cs) ∧
(classify cs = trend_down → allStepsAreDown cs).
```

「依次同向」限定词被真正执行。

Lean 模块：[`Chanlun.TrendType`](lean/Chanlun/TrendType.lean)。

---

## §9 笔可达域确定性

### `noAdjBarContainment`

K 线层面的 `noAdjContainment` 提升。在包含处理后的可达域上成立。

### 定理 9.1（`fractals_alternate_on_containment_free`）

```
∀ bars, noAdjBarContainment bars → AlternateKinds (fractalKinds bars).
```

在可达（无包含）域上，分型种类严格交替 —— 所以三种笔端点读法
（leftmost / extremal / keep-latter）在每个可达输入上**完全重合**。
对任意输入的 gate 相对性发现（44–55% 不一致率）是输入域编码的伪影；
**在可达域上缠论的唯一性主张是真实的**。

证明链：

1. `dichotomy_of_no_containment` —— 任何不包含的对在 `h` 和 `l` 都严格
   单向（`goesUp` 或 `goesDown`）。
2. `neither_preserves_direction` —— 无包含输入上 `.neither` 窗口强制
   `dir(b, c) = dir(a, b)`。
3. `fractalKinds_first_kind_after_{up,down}` —— 先导方向强制首次发射
   种类。
4. 主定理归纳。

Lean 模块：
[`Chanlun.BiReachableDeterminism`](lean/Chanlun/BiReachableDeterminism.lean)。

---

## §10 级别递归（24 课） —— 「走势必完美」

### `centerSize`

```
centerSize c := c.end_ + 1 − c.start.
```

### 定理 10.1（`centerSize_ge_3`）

`zhongshu` 发射的每个中枢满足 `centerSize c ≥ 3`。`extendEnd_ge`
（定理 7.3）的直接推论：扩展从 `i + 3` 开始，不会早于 `i + 2`
返回，所以 `end_ ≥ start + 2` 且 `size ≥ 3`。

### 定理 10.2（`lift_strict_drop`）

```
∀ els g, zhongshu els g 0 ≠ [] →
  (zhongshu els g 0).length + 2 ≤ ((zhongshu els g 0).map centerSize).sum.
```

若任何中枢形成，下一级元素数至少下降 2。配合 `ℕ` 在 `els.length` 上的
良基性，级别递归在 ≤ `n / 2` 级别内终止 —— **「走势必完美」（24 课）的
形式内容**。

Lean 模块：
[`Chanlun.LevelRecursion`](lean/Chanlun/LevelRecursion.lean)。

---

## §11 走势分解（17 课）

### `decompose : List Center → List Walk`

走中枢序列，在每一步发射**极大** Walk：

* 单个中枢剩下 → `consolidation`；
* 极大向上 stepping 的 run → `trend_up`；
* 极大向下 stepping 的 run → `trend_down`。

边界规则：当加上下一个中枢会改变 WalkType（或打破同向不变量）的那一刻，
新 Walk 启动。

### 定理 11.1（`decompose_partition`）

```
Σ (walks.map walkSize) = centers.length.
```

每个中枢索引恰好属于一个 Walk。

### 定理 11.2（`decompose_monotonic`）

Walk 边界在 `start` 上严格递增：对相邻 walk `w₁, w₂`，
`w₁.end_ + 1 = w₂.start`。

### 定理 11.3（`decompose_type_homogeneous`)

每个发射的 Walk 有齐次 WalkType：Walk 跨度内的每个中枢都按 Walk 的
类型分类。`decompose` 不能发射 `mixed` WalkType（由 split 准则证得）；
`mixed` 仅来自下游 merge —— 列为后续工作。

Lean 模块：
[`Chanlun.WalkDecomposition`](lean/Chanlun/WalkDecomposition.lean)。

---

## §12 其它已形式化的层

后续提交增加的模块包括：

* `Chanlun.StrokesIsValidBiCorollary`（`strokes_isValidBi`、
  `strokes_iff_IsValidBi`） —— `strokes_unique` 的非空 + 双向。
* `Chanlun.BiEndpointSubResidues` —— 关闭与 `Chanlun.StrokeUniqueness`
  相关的三个子结果：TO 端点最左 vs 极值、drop-branch 保持、输出顺序
  交替性提升。
* `Chanlun.BiReachableDeterminismBridge` —— §9 交替定理的
  `Interval → Bar` 管道。
* `Chanlun.ZhongshuExtension` —— 四向命名转移（延伸 / 扩展 / 新生 /
  endNoRebirth）+ 9-段升级触发。
* `Chanlun.Beichi` —— 背驰力度比较（24/27/29 课），整数精确位移 +
  斜率。
* `Chanlun.PanzhengBeichi` —— 盘整背驰（37 课）单中枢 A-vs-C 分类器。
* `Chanlun.ThirdBuysell` —— 第三类买卖点（20 课）。
* `Chanlun.FirstSecondBuysell` —— 第一/第二类买卖点（24 课）+
  measure-gate 继承。
* `Chanlun.RecursiveSubBspBeichi` —— 递归三买卖 + 背驰（20/24/27/29 课
  推广至次级别）。
* `Chanlun.IntervalNesting` —— 65/66 课区间套基础分类器和严格下降终止
  测度。

---

## §13 开放问题

尚未在 Lean 库中证明的限制与开放问题列在 [`README.zh.md`](README.zh.md)
的「已知限制与待证问题」中。每条都明示，而非隐藏。

---

## §14 致谢

缠论本身属于缠中说禅的传承。上述形式系统和 `lean/Chanlun/` 下的 Lean
编码是本仓库的贡献。可达域审计修正（§9）和 lift 终止测度（§10）是
形式化的非显然数学贡献；其余都是发表理论的 Lean 形式。

---

## §15 许可

形式化、本文档、参考实现脚本和 CI 工作流按 MIT 许可发布；如有
`LICENSE` 文件以其为准。
