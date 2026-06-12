# 缠论 —— 一份数学教科书

> 以数学家与学生的视角阅读缠论。下列每条**定义**与**定理**均按三段式
> 给出：自然语言陈述、严格形式、`lean/Chanlun/` 下可验证的 Lean 对应。
> 凡原文确有歧义、或 Lean 证明尚未完成之处，均按可外部审计的理由明示
> 其开放状态。
>
> English version: [chanlun.md](chanlun.md).

---

## §0 记号与范围

本文将缠论视为一维离散时间价格序列上的数学理论。价格以整数到达
（如 0.25 跳点的合约按 4 放大，使最小单位为 1）；时间以 ℕ 索引。在
ℤ 上工作避免了浮点不确定性，并使每条定理可判定。

研究对象：

- **K 线**（bar）是一对 (h, l) ∈ ℤ × ℤ 且 h ≥ l，记录一个周期的最高
  与最低价。类型：`Bar := { h : ℤ, l : ℤ }`。
- **区间**（interval）是同样的数据，字段顺序互换，用于包含归一算法：
  `Interval := { l : ℤ, h : ℤ }`，通过 `toBar : Interval → Bar` 桥接。
- **分型**（fractal）是带索引和种类的 K 线，种类取自
  {top, bottom, neither}：
  `Fractal := { idx : ℕ, kind : FractalKind, h : ℤ, l : ℤ }`。
- **笔**（stroke）`{ from_idx, to_idx : ℕ, dir : {up, down} }`。
- **中枢**（center）`{ start, end_ : ℕ, ZD, ZG : ℤ }`，索引区间与重叠
  区间 [ZD, ZG]。
- **走势**（walk）是中枢列表的一个连续子区间附带走势类型标签。

缠论描述的，是 K 线如何组合成分型、分型如何组合成笔、笔如何组合成
线段、线段如何组合成中枢、中枢如何组合成走势，再经递归将整个层级体系
提升到更高层。本文沿此次第展开。

---

## §1 包含处理 —— 算法 N

### 定义 1.1（包含关系）

**叙述。** 相邻 K 线处于*包含关系*指其中之一在高、低两端均被另一者
完全包住 —— 较小者不携带新信息。包含关系必须先被处理掉，序列的分型
形态才可读。

**形式。** 相邻区间 (a, b) 满足包含关系，当且仅当

    (b.l ≤ a.l ∧ a.h ≤ b.h) ∨ (a.l ≤ b.l ∧ b.h ≤ a.h).

列表 xs : List Interval 满足 `noAdjContainment` 当且仅当任何相邻对都
不在包含关系中。

**Lean 实现。** `Chanlun.Normalize.contained`、
`Chanlun.Normalize.noAdjContainment`，位于
[`lean/Chanlun/Normalize.lean`](lean/Chanlun/Normalize.lean)。

### 定义 1.2（单次扫描 `normalize`）

**叙述。** 自左向右扫描 K 线列表，维护一个带方向标志的栈。当下一根
K 线被栈顶包含时，上升趋势取双方高、低的 max；下降趋势取 min；否则
入栈并更新方向。

**形式。**

    pushOne : (stack, up) → bar →
      若 up ∧ contained(stack.top, bar) 则 ([max h, max l] :: stack.tail, up)
      若 ¬up ∧ contained(stack.top, bar) 则 ([min h, min l] :: stack.tail, up)
      否则 (bar :: stack, h(bar) > h(stack.top)).

    normalize : List Interval → List Interval × Bool := foldl pushOne ([], true).

**Lean 实现。** `Chanlun.Normalize.pushOne`、
`Chanlun.Normalize.normalize`。

### 定理 1.3 —— `normalize_no_adjacent_containment`

**叙述。** 单次自左向右扫描即可产生无包含的输出。无需第二次扫描 ——
方向感知的合并规则足够强。

**形式。** 对每个 xs : List Interval，

    noAdjContainment (normalize xs).1.

**Lean 证明。**
[`Chanlun.Normalize.normalize_no_adjacent_containment`](lean/Chanlun/Normalize.lean)。
证明经 `pushOne_preserves`：携带 `noAdjContainment` 与 `goodStack` 方向
一致性的归纳不变量。

---

## §2 分型 —— 定义 3

### 定义 2.1（顶分型 / 底分型）

**叙述。** 给定三根连续的归一 K 线，若中间一根在高、低两端均严格大于
两邻，则为**顶**；若均严格小于两邻，则为**底**；否则为 **neither**。顶
与底标记序列的候选拐点。

**形式。** 对 K 线 a, b, c：

    isTopFractal a b c    := b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l
    isBottomFractal a b c := b.h < a.h ∧ b.h < c.h ∧ b.l < a.l ∧ b.l < c.l

    classifyDef3 a b c := if isTopFractal a b c    then top
                          else if isBottomFractal a b c then bottom
                          else neither.

**Lean 实现。** `Chanlun.Fractal.isTopFractal`、
`Chanlun.Fractal.isBottomFractal`、`Chanlun.Fractal.classifyDef3`，
位于 [`lean/Chanlun/Fractal.lean`](lean/Chanlun/Fractal.lean)。

### 定理 2.2 —— `def3_trichotomy`

**叙述。** 每一个 3 K 线窗口被分类为 {top, bottom, neither} 中的恰好
一种：分类是 total，且 top/bottom 互斥。

**形式。** 对所有 K 线 a, b, c，

    classifyDef3 a b c ∈ {top, bottom, neither}
    ∧ ¬ (isTopFractal a b c ∧ isBottomFractal a b c).

**Lean 证明。** `Chanlun.Fractal.def3_trichotomy`。按严格比较的可判定
性做案例分析。

### 定理 2.3 —— `fractal_slot_equiv_def3`

**叙述。** 算子端的整数编码分类器（0 = top、1 = bottom、2 = neither）
与叙述端的分类器在每个输入上一致。两种"找分型种类"的写法不可能冲突。

**形式。** 令 `kindToInt : FractalKind → ℤ` 把 top ↦ 0、bottom ↦ 1、
neither ↦ 2，`fractalSlotPredicate` 为算子端的整数分类器：

    ∀ a b c : Bar, fractalSlotPredicate a b c = kindToInt (classifyDef3 a b c).

**Lean 证明。** `Chanlun.Fractal.fractal_slot_equiv_def3`。两侧展开后
作 9 路案例分析。

### 定理 2.4 —— `pipeline_inclusion_normalized`（与 §1 的组合）

**叙述。** 算法 N 运行之后，输出中每个内部 3 K 线窗口都是*包含归一*
的：相邻两侧不存在彼此包含关系。所以定义 2.1 在算法 N 之后无歧义
适用。

**形式。** 对所有 xs : List Interval 与所有形如

    (normalize xs).1 = a :: b :: c :: rest

的后缀分解，有
`isInclusionNormalized (toBar b) (toBar a) (toBar c)`。

**Lean 证明。**
[`Chanlun.Pipeline.pipeline_inclusion_normalized`](lean/Chanlun/Pipeline.lean)。
桥接引理 `not_contained_iff_bar` 加上从
`normalize_no_adjacent_containment` 中提取头部对。

### 定理 2.5 —— `pipeline_fractal_classification_well_defined`

**叙述。** 结合定理 1.3、2.2、2.4：在算法 N 之后的任何输出上，每个
内部 3 K 线窗口的种类都是确定的。

**Lean 证明。**
`Chanlun.Pipeline.pipeline_fractal_classification_well_defined`。

---

## §3 笔 —— 定义 4

### 定义 3.1（最左贪心的笔构造）

**叙述。** 走分型列表，维护至多一个*锚点*。每个同向到达的分型把锚点
更新到更"极值"的代表；反向到达且与锚点的间隔 ≥ δmin 的分型，发射一
笔（锚点 → 当前）并重锚；间隔 < δmin 的反向分型被丢弃。

**形式。** 状态 `s = { anchor : Option Fractal, out : List Stroke }`。

    step δmin s f :=
      match s.anchor with
      | none    ⇒ { anchor := some f, out := s.out }
      | some a  ⇒
        if a.kind = f.kind then { anchor := some (pickRep a f), out := s.out }
        else if f.idx - a.idx ≥ δmin then
          { anchor := some f, out := { from_idx := a.idx, to_idx := f.idx, dir := emitDir f } :: s.out }
        else s  -- 丢弃

    strokes frs δmin := reverse (foldl (step δmin) StrokeState.empty frs).out.

**Lean 实现。** `Chanlun.Stroke.step`、`Chanlun.Stroke.strokes`，位于
[`lean/Chanlun/Stroke.lean`](lean/Chanlun/Stroke.lean)。

### 定理 3.2 —— `stroke_emits_separated`（性质 B：间隔性）

**叙述。** 每条发射的笔至少跨过 δmin 个单位。最小间隔门是真正起
作用的。

**形式。**

    ∀ frs δmin, ∀ s ∈ strokes frs δmin, δmin ≤ s.to_idx - s.from_idx.

**Lean 证明。** `Chanlun.Stroke.stroke_emits_separated`，经
`List.mem_reverse` 提升到用户面输出 `Chanlun.Stroke.strokes_separated`。

### 定理 3.3 —— `stroke_emits_alternate`（性质 A：交替性）

**叙述。** 输出中相邻两笔方向相反。走势真正在锯齿状摆动。

**形式。**

    ∀ frs δmin, allAlternate ((foldl (step δmin) StrokeState.empty frs).out).

**Lean 证明。** `Chanlun.Stroke.stroke_emits_alternate`。`reverse` 之后
的用户面提升是
`Chanlun.BiEndpointSubResidues.strokes_alternate`，经 `allAlternate_reverse`。

### 定理 3.4 —— `strokes_unique`（引理 2 的强形式）

**叙述。** 任何在结构上合法的笔序列 —— from 端点是同向 run 的极值代表，
to 端点是最左可接纳的反向分型 —— 必须等于规范的流式输出。贪心构造没有
做任意选择：它是**唯一**的分解。

**形式。** 令 `IsValidBi` 为捕获结构约束的递归谓词，

    ∀ frs δmin alt, IsValidBi frs δmin alt → alt = strokes frs δmin.

**Lean 证明。** `Chanlun.StrokeUniqueness.strokes_unique`，位于
[`lean/Chanlun/StrokeUniqueness.lean`](lean/Chanlun/StrokeUniqueness.lean)。
证明走广义化的 fold-vs-alt 不变量 `fold_consumes_alt`，沿 `frs` 归纳。
非空性（对每个输入都存在合法 `alt`）由
`Chanlun.StrokesIsValidBiCorollary.strokes_isValidBi` 给出；双向版本
`IsValidBi ↔ alt = strokes ...` 是
`Chanlun.StrokesIsValidBiCorollary.strokes_iff_IsValidBi`。

### 定理 3.5 —— 端点子结果

**叙述。** 三条小而承重的等价命题支撑定理 3.4：(a) 在可达输入上，
"最左可接纳的反向分型"读法等于"极值字面"读法；(b) 丢弃分支不改变 fold
状态；(c) 反转输出保持交替性。

**形式。**

    (a) to_endpoint_leftmost_eq_extremal_on_reachable
        : 在严格交替的可达列表上两种读法一致。
    (b) dropBranch_step_no_op  : step δmin s f = s（在丢弃分支上）。
    (c) allAlternate_reverse   : allAlternate l → allAlternate l.reverse.

**Lean 证明。** 位于
[`lean/Chanlun/BiEndpointSubResidues.lean`](lean/Chanlun/BiEndpointSubResidues.lean)：
`to_endpoint_leftmost_eq_extremal_on_reachable`、
`dropBranch_step_no_op`、`dropBranch_preserves_IsValidBi`、
`allAlternate_reverse`，以及提升 `strokes_alternate`。

### 定理 3.6 —— `fractals_alternate_on_containment_free`（可达域确定性）

**叙述。** 在可达域上 —— 即无相邻包含的 K 线列表，也恰恰是算法 N 的
输出 —— 分型种类严格交替。因此三种先验不同的笔端点读法（leftmost /
extremal / keep-latter）在每个可达输入上**完全重合**。在任意输入上
观察到的不一致是输入域编码的伪影，而非缠论本身的歧义。

**形式。**

    ∀ bars : List Bar, noAdjBarContainment bars → AlternateKinds (fractalKinds bars).

**Lean 证明。**
[`Chanlun.BiReachableDeterminism.fractals_alternate_on_containment_free`](lean/Chanlun/BiReachableDeterminism.lean)。
证明链：

1. `dichotomy_of_no_containment`：任意不包含对在 h 和 l 都严格单向。
2. `neither_preserves_direction`：无包含输入上 `.neither` 窗口强制
   方向延续。
3. `fractalKinds_first_kind_after_{up,down}`：先导方向强制首次发射
   种类。
4. 主定理对 K 线列表归纳。

将 §1 的归一化与此交替定理串接的用户面推论是
`Chanlun.BiReachableDeterminismBridge.normalize_then_fractals_alternate`。

### 定理 3.7 —— `bi_to_endpoint_first_admissible` —— 多解，**类 A**

**叙述。** 在任意输入上，原文真正支持两种 TO 端点读法：取最左可接纳
（满足 gap ≥ δmin）的反向分型（`StrokeUniqueness` 采用的读法）；
或取整个 to 侧同向 run 的极值（字面更强的读法）。两种读法是同一条
原文定义的实现细节兄弟，不是两种语义理论。

**形式化（歧义见证）。** 在非可达输入上，若某个同向 run 长度 > 1，
两种读法挑出不同端点 —— 最左可接纳 vs 极值字面。可达情形是构造性
坍塌（见下）。

**Lean 见证。** 构造性歧义隐含在
[`Chanlun.BiEndpointSubResidues`](lean/Chanlun/BiEndpointSubResidues.lean)
中 `toEndpoint_extremal_literal` 与基于 `step` 的最左读法之间。

**类。** **A**（可坍塌）—— gap 是纯输入域伪影。算法 N 把输入归一化
到无相邻包含 K 线列表（定理 1.3），其上分型序列严格交替（定理 3.6），
其上每个同向 run 的长度都是 1，故最左 = 极值平凡成立。

**坍塌条件。** 分型列表严格交替：

    ∀ f g，列表中相邻 (f, g) ⇒ f.kind ≠ g.kind.

等价地：输入 K 线满足 `noAdjBarContainment`，即来自 `normalize` 的
输出。

**坍塌定理（Lean）。**
[`Chanlun.BiEndpointSubResidues.to_endpoint_leftmost_eq_extremal_on_reachable`](lean/Chanlun/BiEndpointSubResidues.lean) ——
在任意严格交替的分型序列上，字面极值 TO 端点 = 最左可接纳端点。
与
[`Chanlun.BiReachableDeterminism.fractals_alternate_on_containment_free`](lean/Chanlun/BiReachableDeterminism.lean)
组合，坍塌在所有可达（post-`normalize`）输入上成立。

---

## §4 线段 —— 定义 5–16 + 定理 1

### 定义 4.1（BoundedFix 递归）

**叙述。** 线段把笔索引区间 [a, n) 划分为共享特征方向的极大连续子区间。
递归发射器以*推进预言* `find_term` 为参数，返回下一个最左 ≥ a 的终止
索引。

**形式。** 给定 `find_term : ℕ → Option ℕ` 与契约
`find_term_ge : ∀ a j, find_term a = some j → a ≤ j`，

    segments find_term find_term_ge a n :=
      if h : a ≥ n then []
      else match h' : find_term a with
        | none   ⇒ [⟨a, n - 1⟩]
        | some j ⇒ ⟨a, j⟩ :: segments find_term find_term_ge (j + 1) n.

终止由严格下降 `n - (j + 1) < n - a` 保证。

**Lean 实现。** `Chanlun.Segment.segments`，位于
[`lean/Chanlun/Segment.lean`](lean/Chanlun/Segment.lean)。完整的特征
序列 Φ + 重叠 admissibility 内部细节在此未重新推导；Lean 递归只需要
最左 ≥ a 的契约。

### 定理 4.2 —— `segment_advance_strictly_increasing`

**叙述。** 核心终止引理。每当 `find_term a` 返回某个 j 且 a ≤ j，
测度 n − a 在递归步骤上严格下降。

**形式。**

    find_term a = some j → a ≤ j → n - (j + 1) < n - a.

**Lean 证明。** `Chanlun.Segment.segment_advance_strictly_increasing`。
短整数算术。

### 定理 4.3 —— `segments_partition`（性质 P）

**叙述。** 发射的线段连续平铺 [a, n) —— 每个索引恰属于一条线段。

**形式。**

    ∀ a n, partitionFrom (segments find_term find_term_ge a n) a n.

**Lean 证明。** `Chanlun.Segment.segments_partition`，经强形式
`segments_partitionFrom`。

### 定理 4.4 —— `segments_terminate`（性质 T）

**叙述。** 至多发射 n − a + 1 条线段；递归产生有限列表。

**形式。**

    ∀ a n, (segments find_term find_term_ge a n).length ≤ n - a + 1.

**Lean 证明。** `Chanlun.Segment.segments_terminate`，经
`segments_length_le`。

### 定理 4.5 —— 预言接口的非空性

**叙述。** 平凡推进预言 `a ↦ some a` 满足最左 ≥ a 的契约，故递归
非空地可实例化。

**形式。**

    ∃ find_term, ∀ a j, find_term a = some j → a ≤ j.

**Lean 证明。** `Chanlun.Segment.find_term_contract_nonvacuous`，由
`trivialFindTerm` 见证。

### 状态 —— 定理 1（参数化唯一分解）

**开放。** 原文定理 1 主张线段分解对一类满足 Φ-重叠-admissibility 的
预言是**唯一**分解。Lean 编码抽象地解决了最左 ≥ a 契约下的递归，并
给出对任何固定 `find_term` 的确定性（函数即定义）。剩下的参数化唯一性
—— 任意两个满足原文 Φ-重叠-admissibility 规范的预言产生相同线段列表
—— 命名为 `[chanlun_segment_phi_uniqueness_OPEN]`，因为原文未唯一
固定 Φ；备选读法列于 [`README.md`](README.md) 的「已知限制」。

---

## §5 中枢 —— 17/20 课

### 定义 5.1（中枢形成）

**叙述。** 当三个连续子元素共享一个非空重叠区间时形成一个中枢。从
i = 0 开始扫描：若至少剩三个元素，取

    ZD := max(els[i].lo, els[i+1].lo, els[i+2].lo)
    ZG := min(els[i].hi, els[i+1].hi, els[i+2].hi).

若 ZD ≤ ZG（真重叠），发射中枢 ⟨i, extendEnd(i+3), ZD, ZG⟩ 并在
extendEnd 之后续；否则滑动 i := i + 1。

**形式。**

    zhongshu els g i :=
      if els.length ≤ i + 2 then []
      else
        let ZD := max ... ; let ZG := min ...
        if ZD ≤ ZG then ⟨i, extendEnd ..., ZD, ZG⟩ :: zhongshu els g (extendEnd + 1)
        else zhongshu els g (i + 1).

**Lean 实现。** `Chanlun.Zhongshu.zhongshu`，位于
[`lean/Chanlun/Zhongshu.lean`](lean/Chanlun/Zhongshu.lean)。

### 定义 5.2（扩展与 zone 门）

**叙述。** 扩展函数 `extendEnd g zd zg j` 在第 j 个元素与活动 zone
重叠时向前走 j。参数 g : ZoneGate ∈ {first3, all_} 控制活动 zone
是否随新元素加入而再收紧：

- `first3` 把 zone 固定在初始 (ZD, ZG)；
- `all_` 每步收紧为 (max zd els[j].lo, min zg els[j].hi)。

原文对此选择未明确，我们提供两种读法并证明两者均合法。

**Lean 实现。** `Chanlun.Zhongshu.extendEnd`、`Chanlun.Zhongshu.ZoneGate`。

### 定理 5.3 —— `zhongshu_valid`

**叙述。** 每个发射的中枢都有良形 zone（ZD ≤ ZG）。

**形式。**

    ∀ els g i, ∀ c ∈ zhongshu els g i, c.ZD ≤ c.ZG.

**Lean 证明。** `Chanlun.Zhongshu.zhongshu_valid`。构造性的形成门
`ZD ≤ ZG` 守护每次发射。

### 定理 5.4 —— `zhongshu_disjoint`

**叙述。** 相邻中枢索引区间不重叠：c₁.end_ < c₂.start。

**形式。**

    ∀ els g i, DisjointConsec (zhongshu els g i).

**Lean 证明。** `Chanlun.Zhongshu.zhongshu_disjoint`，经
`zhongshu_head_start_ge` 串接。

### 定理 5.5 —— `extendEnd_ge`（扩展终止）

**叙述。** 扩展索引不会倒退：extendEnd(j) ≥ j − 1。这是赋予
`zhongshu` 在 els.length − i 上良基性的测度。

**形式。**

    ∀ els g zd zg j, j - 1 ≤ extendEnd els g zd zg j.

**Lean 证明。** `Chanlun.Zhongshu.extendEnd_ge`。

### 定义 5.6（四向转移：延伸 / 扩展 / 新生 / endNoRebirth）

**叙述。** 当一个新元素到来于刚发射的中枢之后，发生四种命名事件之一：
**延伸**（在核心 [ZD, ZG] 内扩展）、**扩展**（在外包络 [DD, GG] 内
扩展）、**新生**（一个新的不相交中枢开始）、**endNoRebirth**（序列
结束而无新生）。当同一中枢内累计 9 个子元素时，**升级**信号触发 ——
中枢已足够大以提升到更高层（30 课）。

**形式。** 令 `upgradeSegments := 9` 且 `CenterExt` 同时持有核心
(ZD, ZG) 和外包络 (DD, GG)，

    classifyExtension : CenterExt → Element → List Element → ExtensionEvent.

**Lean 实现。** `Chanlun.ZhongshuExtension.classifyExtension`，位于
[`lean/Chanlun/ZhongshuExtension.lean`](lean/Chanlun/ZhongshuExtension.lean)。

### 定理 5.7 —— 扩展分类是 total 的

**叙述。** 每个输入恰落入一个命名事件类 —— 分类 total 且绝不静默。

**形式。**

    ∀ c e post, classifyExtension c e post ∈
        {extension, expansion, rebirth, endNoRebirth, upgrade}.

**Lean 证明。** `Chanlun.ZhongshuExtension.classifyExtension_total`。

### 定理 5.8 —— 核心与外包络的承重性

**叙述。** 延伸事件保持核心 (ZD, ZG)；扩展事件加宽外包络 (DD, GG)；
新生事件创建一个与旧中枢不相交的新核心。

**形式。**

    extension_preserves_core_ZD_ZG : 返回 extension ⇒ (ZD, ZG) 不变。
    expansion_widens_GG_DD         : 返回 expansion ⇒ DD' ≤ DD ∧ GG ≤ GG'。
    rebirth_creates_disjoint_core  : 返回 rebirth ⇒ 新核心与旧不相交。

**Lean 证明。** `extension_preserves_core_ZD_ZG`、
`expansion_widens_GG_DD`、`rebirth_creates_disjoint_core`，均位于
`Chanlun.ZhongshuExtension`。

### 定理 5.9 —— `upgrade_trigger_iff_9_segments`

**叙述。** 9 段升级信号当且仅当子元素计数越过阈值时触发；与下一个
到达元素的值无关。

**形式。**

    classifyExtension c e post = upgrade ↔ subSegmentCount c ≥ 9.

**Lean 证明。** `upgrade_trigger_iff_9_segments` 与
`upgrade_trigger_element_independent`。

### 定理 5.10 —— `zhongshu_zone_gate_divergence_witness`（构造性歧义见证）—— 多解，**类 A**

**叙述。** first3 与 all_ 门（定义 5.2）真正是多值的，并非记号上的
小别。原文按"前 3 段"刻画中枢的 ZD/ZG，但对 ZD/ZG 是否随后续重叠
元素 RE-收紧没有给死：`first3` 把 zone 固定，`all_` 让 zone 随每个
被接纳的元素继续收紧。两种读法都产生合法（ZD ≤ ZG）且不相交的中枢
列表，只是对那些"严格收紧 zone 的元素"作出了不同的接纳判定。

**形式化（歧义见证）。** 取

    els := [⟨0, 10⟩, ⟨3, 13⟩, ⟨5, 8⟩, ⟨7, 12⟩, ⟨5, 6⟩]

（见 `Chanlun.DivergenceWitnesses.zoneGateWitnessEls`），

    ∃ zd zg zd' zg' e, overlapsZone zd zg e ∧ ¬ overlapsZone zd' zg' e.

见证 (5, 8)（first3 zone）vs (7, 8)（all_ 收紧后的 zone），元素 ⟨5, 6⟩：
6 ≥ 5 成立但 6 ≥ 7 失败。两个门的合法性由配套定理
`zhongshu_zone_gate_witness_valid_disjoint` 给出。这把经验观察到的
约 12% 不一致率提升为 Lean 级的构造性见证。

**Lean 见证。**
[`Chanlun.DivergenceWitnesses.zhongshu_zone_gate_divergence_witness`](lean/Chanlun/DivergenceWitnesses.lean)。

**类。** **A**（可坍塌）—— 两个门只在"某个被接纳的后续元素严格收紧
zone"时才不一致。如果每个被接纳的元素都把 first3 的 zone 完全包住，
两条递归在每一步都保持同步。

**坍塌条件。** 每个后续元素都 CONTAIN 住 first3 的 zone —— 对于固定
的 `(zd, zg)` 与每个被检视的索引 k ≥ j，

    (els.get k).lo ≤ zd  ∧  (els.get k).hi ≥ zg.

等价地：`all_` 那一步的收紧 `max zd e.lo, min zg e.hi` 对每个被接纳
的元素都是 NO-OP。

**坍塌定理（Lean）。**
[`Chanlun.CollapseTheorems.zhongshu_zone_gate_collapses_when_no_tightening`](lean/Chanlun/CollapseTheorems.lean) ——
对任意满足 `ContainsZoneFrom els zd zg j` 的元素列表，`first3` 与
`all_` 两条 `extendEnd` 递归返回相同的 end 索引。强归纳证明在每个递归
层都维持「收紧参数始终相等」的不变量。

### 定理 5.11 —— 贴边情形（`≤` vs 严格 `<`）—— 多解，**类 A**

**叙述。** 17 课第 3 行原文说下一个元素「重叠」zone，而 17 课例题
计算用了严格边界检查。重叠谓词的两种读法是

    overlapsLE zd zg e : e.lo ≤ zg ∧ e.hi ≥ zd     （规范，≤）
    overlapsLT zd zg e : e.lo < zg ∧ e.hi > zd     （兄弟，严格 <）

本仓库取 ≤ 为规范（匹配 `Chanlun.Zhongshu.extendEnd` 的实现）；严格
< 版本是一个兄弟 oracle，其行为在「贴边」元素上分歧。

**形式化（歧义见证）。** 任何 `e.lo = zg` 的元素满足 `overlapsLE`
但不满足 `overlapsLT` —— 具体地 `e = ⟨zg, h⟩`（任意 `h ≥ zd`）。
两种读法在该元素上分歧。

**Lean 见证。** 构造性 —— 贴边元素就是分歧见证；显式 `decide`-可
检查的例子是直接的。

**类。** **A**（可坍塌）—— 分歧只发生在「正好坐在 `e.lo = zg` 或
`e.hi = zd` 边界上」的元素。所有元素都不贴边时两种读法坍塌为一种。

**坍塌条件。** 每个后续元素都不贴边：

    ∀ k ≥ j，k < els.length ⇒
      (els.get k).lo ≠ zg  ∧  (els.get k).hi ≠ zd.

**坍塌定理（Lean）。**
[`Chanlun.CollapseTheorems.zhongshu_shoulder_collapses_off_boundary`](lean/Chanlun/CollapseTheorems.lean) ——
在 `OffShoulder zd zg e` 下，`overlapsLE zd zg e ↔ overlapsLT zd zg e`。
列表层的提升
[`zhongshu_shoulder_collapses_off_boundary_list`](lean/Chanlun/CollapseTheorems.lean)
把等价性传播到输入序列上每个不贴边元素。

---

## §6 走势 —— 类型与分解（17 课）

### 定义 6.1（WalkType 与 stepDir）

**叙述。** 相邻两中枢之间的方向：若下一中枢的 ZD 严格大于上一中枢的
ZG 为 `up`；若下一 ZG 小于上一 ZD 为 `down`；否则为 `neither`。中枢
列表按其步幅模式分类为 `consolidation`、`trend_up`、`trend_down`、
`mixed` 或 `none_`。

**形式。**

    stepDir prev cur := if prev.ZG < cur.ZD then up
                        else if cur.ZG < prev.ZD then down
                        else neither

    classify : List Center → WalkType
    classify []           = none_
    classify [_]          = consolidation
    classify (c₁::c₂::rs) = if allUp  then trend_up
                            else if allDown then trend_down
                            else mixed.

**Lean 实现。** `Chanlun.TrendType.stepDir`、
`Chanlun.TrendType.classify`，位于
[`lean/Chanlun/TrendType.lean`](lean/Chanlun/TrendType.lean)。

### 定理 6.2 —— `classify_total`

**叙述。** 分类 total：每个中枢列表恰好落入
{none_, consolidation, trend_up, trend_down, mixed} 中之一。

**形式。**

    ∀ cs : List Center, classify cs ∈ {none_, consolidation, trend_up, trend_down, mixed}.

**Lean 证明。** `Chanlun.TrendType.classify_total`。

### 定理 6.3 —— `classify_trend_monotone`

**叙述。** 趋势标签不静默 —— 它强制依次同向。

**形式。**

    (classify cs = trend_up   → allStepsAreUp   cs)
    ∧ (classify cs = trend_down → allStepsAreDown cs).

**Lean 证明。** `Chanlun.TrendType.classify_trend_monotone`，经双向
`allUp_iff_allStepsAreUp` 与 `allDown_iff_allStepsAreDown`。

### 定义 6.4（走势分解）

**叙述。** 给定中枢列表，`decompose` 将其划分为极大走势。单个残留
中枢成为 `consolidation`；连续 `up` 步形成 `trend_up` 走势；连续
`down` 步形成 `trend_down` 走势。新走势在加入下一个中枢会改变走势
类型的那一刻启动。

**形式。** 令 `extendRun centers d j` 在步方向等于 d 时向前走 j，

    decompose : List Center → List Walk.

**Lean 实现。**
[`Chanlun.WalkDecomposition.decompose`](lean/Chanlun/WalkDecomposition.lean)。

### 定理 6.5 —— `decompose_partition`

**叙述。** 发射的走势恰好平铺中枢列表：每个中枢索引属于一个走势。

**形式。**

    Σ (walks.map walkSize) = centers.length.

**Lean 证明。** `Chanlun.WalkDecomposition.decompose_partition`。

### 定理 6.6 —— `decompose_monotonic`

**叙述。** 走势边界串接：每个走势的 end_ + 1 等于下一走势的 start。

**形式。**

    对所有相邻 (w₁, w₂) ∈ walks，w₁.end_ + 1 = w₂.start.

**Lean 证明。** `Chanlun.WalkDecomposition.decompose_monotonic`，经
`decomposeFrom_chain` 与 `WalksChain` 谓词。

### 定理 6.7 —— `decompose_type_homogeneous`

**叙述。** 每个发射的走势有齐次类型。`trend_up` 走势内每一步都是
`up`；`trend_down` 内每一步都是 `down`。分类器永远不会发射 `mixed`
或 `none_`。

**形式。**

    ∀ w ∈ decompose centers, w.kind ∈ {consolidation, trend_up, trend_down}
    ∧ 走势内所有 stepDir 与 w.kind 一致.

**Lean 证明。** `Chanlun.WalkDecomposition.decompose_type_homogeneous`，
经辅助 `decomposeFrom_type_well_formed`。

### 定理 6.8 —— `decompose_spec_unique_extensional`

**叙述。** `decompose` 是**这个**分解：任何在空输入上与 `decompose`
外延一致、且在索引 0 处行为相同的函数，在每个输入上都等于 `decompose`。

**形式。**

    ∀ f : List Center → List Walk,
      f [] = decompose [] →
      (∀ cs, f cs 在 decompose cs 的头走势上启动) →
      ∀ cs, f cs = decompose cs.

**Lean 证明。** `decompose_unique`、
`decompose_spec_unique_extensional`、`decompose_spec_unique_empty`、
`decompose_spec_unique_head_at_zero`。

### 状态 —— `mixed` 合并

**开放。** 独立的下游合并步骤可以把相邻走势黏合成 `mixed` 超级走势。
我们不在 Lean 库里执行该合并；命名为
`[chanlun_walk_mixed_merge_OPEN]`，列于 [`README.md`](README.md)。

---

## §7 背驰 —— 24/27/29 课

### 定义 7.1（移动、位移、measure）

**叙述。** 方向性移动是三元组 (lo, hi, dur) —— 带显式持续时间的位移
载体。移动的 **力度** 可由位移本身（`disp`）或斜率（`disp / dur`）
度量；原文在不同章节调用两者。我们对命名 `Measure ∈ {disp, slope}`
做参数化。

**形式。**

    Move := { lo : ℤ, hi : ℤ, dur : ℤ }
    disp m := m.hi - m.lo
    lhsRhs a c disp  := (disp a, disp c)
    lhsRhs a c slope := (disp a · c.dur, disp c · a.dur)   -- 整数精确交叉积

**Lean 实现。** `Chanlun.Beichi.Move`、`Chanlun.Beichi.disp`、
`Chanlun.Beichi.lhsRhs`，位于
[`lean/Chanlun/Beichi.lean`](lean/Chanlun/Beichi.lean)。

### 定义 7.2（背驰分类器）

**叙述。** C 比 A 弱（lhs < rhs）—— 背驰；力度相等 —— `tie`；C 强于
A —— `no_beichi`。

**形式。**

    classifyBeichi a c m :=
      let (lhs, rhs) := lhsRhs a c m
      if lhs < rhs then beichi
      else if lhs = rhs then tie
      else no_beichi.

### 定理 7.3 —— `classifyBeichi_total` 与 `beichi_irrefl`

**叙述。** 分类对 {beichi, no_beichi, tie} 是 total 的，且反身性
不成立：一个移动永远不会与自己背驰。

**形式。**

    ∀ a c m, classifyBeichi a c m ∈ {beichi, no_beichi, tie}
    ∀ a m, classifyBeichi a a m ≠ beichi.

**Lean 证明。** `classifyBeichi_total`、`beichi_irrefl`，经辅助
`lhsRhs_self_eq`。

### 定理 7.4 —— `beichi_load_bearing`

**叙述。** 分类器确实在比较力度。在 disp 下，`beichi a c` 等价于
`disp c < disp a`；在 slope 下，等价于整数精确交叉积比较。

**形式。**

    classifyBeichi a c disp  = beichi ↔ disp c < disp a
    classifyBeichi a c slope = beichi ↔ disp c · a.dur < disp a · c.dur.

**Lean 证明。** `beichi_load_bearing_slope`、`beichi_load_bearing_disp`，
合并为 `beichi_load_bearing`。配套的 no-beichi/tie 形式：
`no_beichi_disp_strict`、`no_beichi_slope_strict`、`tie_disp_iff`、
`tie_slope_iff`。

### 定理 7.5 —— `beichi_measure_gate_witness`（构造性歧义见证）—— 多解，**类 B**

**叙述。** disp 与 slope 的选择真正是多值的。原文在不同课节调用两个
measure（24 课用 disp，27 课用 slope），从未指定哪个是规范的 —— 这
对 measure 选择的沉默是真实的语义歧义，不是记号上的。存在移动 a, c
使得 disp 说背驰而 slope 说 no_beichi。

**形式化（歧义见证）。**

    ∃ a c, classifyBeichi a c disp = beichi
         ∧ classifyBeichi a c slope = no_beichi.

来自 `Chanlun.Beichi` 的手工见证：A 在 5 个元素上走 10（slope 2）；
C 在 1 个元素上走 6（slope 6）。disp：`6 < 10` ⇒ 背驰；slope：
`6·5 = 30 > 10·1 = 10` ⇒ no_beichi（C 段更短但更快）。

**Lean 见证。** `Chanlun.Beichi.beichi_measure_gate_witness`，
跨命名空间重新导出为
`Chanlun.DivergenceWitnesses.beichi_measure_gate_divergence_witness`。

**类。** **B**（永远多解 —— 原文的语义 measure 选择）。

**为何不坍塌。** `disp` 与 `slope` 之间的选择是原文留给从业者的
ORACLE 选择。新数据无法决定，因为两个 measure 在回答不同的问题：
disp 问「价格走了多远」，slope 问「单位时间走得多快」。一段"较短
但更快"的走势在一个 measure 下背驰、在另一个 measure 下不背驰，这
是两个事实，不是同一个事实的两种估计 —— 多塞 K 线进来不能宣告哪个
问题才是交易员真正在问的。经验一致率（7 年 NQ 参考上约 82.2%）只能
量化分歧区域的大小，不能裁定胜者。这个门相对于 measure，而不是相对于
数据。

### 定义 7.6（盘整背驰，37 课）

**叙述。** 在单个中枢内，进入中枢的 A 段与离开中枢的 C 段组成一个
`PanzhengTriple`。盘整背驰分类器：在所选 measure 下 C 弱于 A 时声明
panzheng_beichi，否则 no_panzheng_beichi；平衡情形为 incomplete。

**形式。** `classifyPanzheng : PanzhengTriple → Measure → PanzhengVerdict`。

**Lean 实现。** `Chanlun.PanzhengBeichi.classifyPanzheng`，位于
[`lean/Chanlun/PanzhengBeichi.lean`](lean/Chanlun/PanzhengBeichi.lean)。

### 定理 7.7 —— 盘整背驰的 total 与承重性

**叙述。** 分类器 total；在每个 measure 下都真正比较力度；incomplete
判定恰好对应平衡情形。

**形式。**

    classify_panzheng_total       : 每个输入落入四类判定之一。
    panzheng_load_bearing_disp    : panzheng_beichi ⇒ disp c < disp a。
    panzheng_load_bearing_slope   : panzheng_beichi ⇒ 交叉积比较成立。
    panzheng_incomplete_iff       : incomplete ↔ disp c · a.dur = disp a · c.dur（在 slope 下）。

**Lean 证明。** `classify_panzheng_total`、`panzheng_load_bearing_disp`、
`panzheng_load_bearing_slope`、`panzheng_incomplete_iff`。

### 定理 7.8 —— `panzheng_measure_gate_witness` 与 intra-vs-inter —— 多解，**类 B**

**叙述。** 关于盘整背驰的两个进一步构造性见证：(a) disp-vs-slope 门
即使在盘整层次也真实 —— 存在三元组使 disp 说 panzheng_beichi 而 slope
说 no_panzheng_beichi；(b) 在单中枢三元组上使用 inter-中枢 measure 是
一个真正不同的分类器 —— 存在三元组，intra-中枢分类器说
panzheng_beichi 而 inter-中枢变种说 no_panzheng_beichi。两个轴都是
原文留下的语义选择 —— measure 家族 AND 比较所在的 zone。

**形式化（歧义见证）。**

    panzheng_measure_gate_witness : ∃ t, intra-disp = panzheng_beichi ∧ intra-slope = no_panzheng_beichi。
    panzheng_intra_vs_inter_load_bearing : ∃ t, intra ≠ inter-变种.

**Lean 见证。** `panzheng_measure_gate_witness`、
`panzheng_intra_vs_inter_load_bearing`，提升为歧义见证面
`panzheng_measure_gate_propagation_witness`。

**类。** **B**（永远多解）—— 继承定理 7.5 的 measure 选择自由度，
再叠加第二个 oracle 自由度：哪个中枢（SAME 单中枢 vs PREVIOUS
inter-中枢段）提供比较的参考。

**为何不坍塌。** 继承自定理 7.5：disp 与 slope 回答的是不同问题，
新数据不会选择其中一个。intra-vs-inter 这个轴同样是不可化归的语义
选择 —— 37 课对盘整背驰的定义就 RELATIVE 于同一个单中枢（A 进入 C
离开 SAME zone），而 inter-中枢变种把 C 与 PRIOR inter-中枢的 A 段
作比较。这是两个不同的物理主张，不是同一主张的两种近似。选择哪个
就是选择"强度衰减相对于什么"，是一个建模承诺，不是被更多 K 线收敛
的估计。

### MACD 作为辅助 measure（27 课，经验性 grounding）

**叙述。** 27 课明确把 MACD 作为**辅助** measure —— 不是规范的 disp/
slope，而是一种再加工。在 7 年实盘 NQ 1h 数据上，MACD 的背驰判定与
disp 在约 46.4% 的提取 (A, C) 窗口上一致，与 slope 在约 17.9% 上一致。
不一致位置以显式 (a_idx, c_idx, disp_says, macd_says) 见证报告。
不一致本身就是"MACD 是辅助，不是规范"的经验内容。

**Lean 状态。** 开放为 `[chanlun_beichi_macd_measure_lean_OPEN]`：把
`Chanlun.Beichi.Measure` 扩展到第三个构造器 `macd` 在结构上是干净的
（代数延伸；交叉积比较的是 MACD 能量）。grounding 脚本
[`grounding/chanlun_macd_grounding.py`](grounding/chanlun_macd_grounding.py)
计算一致率并发射不一致见证；Lean 构造性提升被命名为开放。

---

## §8 三类买卖点 —— 20、24 课

### 定义 8.1（第一/第二类分类器，24 课）

**叙述。** 一个 `TerminalWindow` 打包中枢间的 A 段、候选回拉段、入场
水平。分类器先问 A 段是否背驰（背景背驰）；若是，声明
`first_buy`/`first_sell`；回拉段随后被测试是否非破首点，若是则升级为
`second_buy`/`second_sell`。回拉破首点为 `first_point_failed`；
静默情形为 `incomplete`。

**形式。** `classifyBsp : TerminalWindow → Measure → BspKind`，其中
`BspKind ∈ {first_buy, first_sell, second_buy, second_sell,
first_point_failed, incomplete}`。

**Lean 实现。** `Chanlun.FirstSecondBuysell.classifyBsp`，位于
[`lean/Chanlun/FirstSecondBuysell.lean`](lean/Chanlun/FirstSecondBuysell.lean)。

### 定理 8.2 —— total 与非破首点

**叙述。** 分类 total。`second_buy` 判定意味着回拉真正没有跌破首点
极值；`second_sell` 对称；`first_point_failed` 意味着回拉确实破点。

**形式。**

    classify_total          : 每个输入的判定 ∈ BspKind。
    second_buy_non_breaking : second_buy  → pull.lo ≥ firstExtreme。
    second_sell_non_breaking: second_sell → pull.hi ≤ firstExtreme。
    first_point_failed_iff  : first_point_failed ↔ 回拉破点。

**Lean 证明。** `classify_total`、`classify_first_point_only_total`、
`second_buy_non_breaking`、`second_sell_non_breaking`、
`second_not_breaking_iff`、`first_point_failed_iff`。

### 定理 8.3 —— `first_second_inheritance_load_bearing` —— 多解，**类 B**

**叙述。** measure-门的传递抵达买卖点层。存在 `TerminalWindow` 使
disp-measure 分类器返回 `second_buy` 而 slope-measure 分类器返回
`incomplete` —— 力度 measure 的选择沿管道传递到面向交易者的判定。
这里的多解性是从定理 7.5 继承的：买卖点分类器在所选 measure 下调用
`classifyBeichi`，所以 measure-门的歧义自然透传。

**形式化（歧义见证）。**

    ∃ w, classifyBsp w disp = second_buy ∧ classifyBsp w slope = incomplete.

**Lean 见证。** `first_second_inheritance_load_bearing`，提升到
`Chanlun.DivergenceWitnesses.first_second_measure_gate_divergence_witness`。

**类。** **B**（永远多解，继承）—— §7 的 disp-vs-slope 语义选择的
下游传递。

**为何不坍塌。** 买卖点判定结构上是「`classifyBeichi w.A w.C m`
再加回拉测试」。因为内层 `classifyBeichi` 是类 B（定理 7.5），外层
分类器继承同样不可化归的 measure 选择。新数据 CAN 缩小 disp-vs-slope
在下游的一致率（当前在 conformance 参考上传播分歧约 5.8%，比上游的
约 17.8% 小），但 CANNOT 消除：只要存在一个窗口 disp 与 slope 在
背景背驰判定上分歧，买卖点分类器就在该窗口分歧。「哪个 measure 定义
一个可交易的买点」是原文不交给数据决定的策略选择。

### 定理 8.4 —— `classify_implies_beichi_and_pull`

**叙述。** 非 incomplete 判定要求所选 measure 下背景背驰成立且回拉段
有定义。

**形式。**

    classifyBsp w m ≠ incomplete → (m 下背驰成立 ∧ pull 有定义).

**Lean 证明。** `classify_implies_beichi_and_pull`。

### 定义 8.5（第三类分类器，20 课）

**叙述。** 中枢完成后，下一离开段要么向上突破 ZG（给出
`third_buy`）、要么向下突破 ZD（`third_sell`）、要么从上方回入
（`reenter_above`）、要么从下方回入（`reenter_below`）。再加一个无
离开段的 incomplete 状态。

**形式。** `classifyBsp : Departure → BspKind`，其中
`BspKind ∈ {third_buy, third_sell, reenter_above, reenter_below,
incomplete}`。

**Lean 实现。** `Chanlun.ThirdBuysell.classifyBsp`，位于
[`lean/Chanlun/ThirdBuysell.lean`](lean/Chanlun/ThirdBuysell.lean)。

### 定理 8.6 —— 第三类的 total 与 zone 含义

**叙述。** 分类 total。`third_buy` 真正意味着离开段向上突破 ZG；
`third_sell` 真正意味着向下突破 ZD。

**形式。**

    classifyBsp_total          : 每个输入的判定 ∈ BspKind。
    bsp_zone_load_bearing_up   : third_buy  → dep.move.lo > c.ZG。
    bsp_zone_load_bearing_down : third_sell → dep.move.hi < c.ZD。

**Lean 证明。** `classifyBsp_total`、`bsp_zone_load_bearing_up`、
`bsp_zone_load_bearing_down`。

### 定理 8.7 —— 递归次级买卖点

**叙述。** 次级别上的第三类分类 total，在有界燃料下终止，并以追踪的
`RecursiveVerdict` 标签继承父级判定。燃料界源自级别递归的严格下降
测度（下方定理 9.2）。

**形式。**

    recursive_subBsp_total           : 每次调用落入四个命名判定之一。
    recursive_subBsp_terminates      : 充足燃料 → 无 incomplete。
    recursive_subBsp_inheritance     : 当子判定一致时，级别 n 判定被保持。
    recursive_subBsp_fuel_stationary : 燃料 ≥ 级别深度后判定燃料不变。
    recursive_subBsp_fuel_bound_via_levelRecursion : 燃料 ≤ n / 2 足够。

**Lean 证明。** 均位于
[`lean/Chanlun/RecursiveSubBspBeichi.lean`](lean/Chanlun/RecursiveSubBspBeichi.lean)：
`recursive_subBsp_total`、`recursive_subBsp_terminates`、
`recursive_subBsp_inheritance`、`recursive_subBsp_fuel_stationary`、
`recursive_subBsp_fuel_bound_via_levelRecursion`。

---

## §9 级别递归 —— 24 课「走势必完美」

### 定义 9.1（`centerSize` 与级别提升）

**叙述。** 每个中枢有大小 `c.end_ + 1 - c.start`，即覆盖的子元素
个数。下一层由把每个中枢提升为承载核心 [ZD, ZG] 的 Element 而成；
`liftStep` 为一轮 `zhongshu` 后跟 `liftCenters`。

**形式。**

    centerSize c   := c.end_ + 1 - c.start
    liftCenter c   := { lo := c.ZD, hi := c.ZG }
    liftCenters cs := cs.map liftCenter
    liftStep els g := liftCenters (zhongshu els g 0)
    levelTower els g 0       := els
    levelTower els g (n + 1) := levelTower (liftStep els g) g n.

**Lean 实现。** 定义位于
[`lean/Chanlun/LevelRecursion.lean`](lean/Chanlun/LevelRecursion.lean)。

### 定理 9.2 —— `lift_strict_drop`（「走势必完美」）

**叙述。** 一旦有任何中枢形成，中枢列表所覆盖的子元素个数至少超过
中枢个数 2。所以提升到下一层严格下降元素个数 —— 由 ℕ 上的良基性，
级别递归在 ≤ n/2 层内终止。这就是 24 课「走势必完美」的形式内容。

**形式。**

    ∀ els g, zhongshu els g 0 ≠ [] →
      (zhongshu els g 0).length + 2 ≤ ((zhongshu els g 0).map centerSize).sum.

**Lean 证明。** `Chanlun.LevelRecursion.lift_strict_drop`。证明把
`centerSize_ge_3`（每个中枢覆盖 ≥ 3 个子元素）与算术
`total_size_ge_3_times_count` 串起来。推论
`level_recursion_count_decreases` 直接打包严格下降。

### 定理 9.3 —— `centerSize_ge_3`

**叙述。** 每个发射的中枢覆盖至少 3 个子元素。`extendEnd_ge`
（定理 5.5）的直接推论：扩展从 i + 3 开始，永远不会早于 i + 2 返回。

**形式。**

    ∀ els g, ∀ c ∈ zhongshu els g 0, 3 ≤ centerSize c.

**Lean 证明。** `Chanlun.LevelRecursion.centerSize_ge_3`。

### 定理 9.4 —— 外包络承重性

**叙述。** 每个提升的 Element 继承其源中枢的良形 zone（lo ≤ hi）。

**形式。**

    liftCenter_lo_le_hi : c.ZD ≤ c.ZG → (liftCenter c).lo ≤ (liftCenter c).hi.
    liftCenters_all_valid : liftCenters (zhongshu els g 0) 中的每个元素都有 lo ≤ hi.
    liftCenters_mem_iff : e ∈ liftCenters cs ↔ ∃ c ∈ cs, e = liftCenter c.

**Lean 证明。** `liftCenter_range_eq_core`、`liftCenter_lo_le_hi`、
`liftCenters_all_valid`、`liftCenters_mem_iff`。

### 定理 9.5 —— 跨层级的确定性保持

**叙述。** 级别提升是确定性的：层 0 上输入相等导致每一层的塔都相等。
次级别上的分歧只能来自层 0 输入的分歧。

**形式。**

    liftStep_deterministic   : els = els' → liftStep els g = liftStep els' g.
    levelTower_deterministic : els = els' → ∀ n, levelTower els g n = levelTower els' g n.
    levelTower_input_eq      : 输入相等 → 塔相等.
    levelTower_agreement_lifts: 层 0 一致沿层级传递.

**Lean 证明。** `liftStep_deterministic`、`levelTower_deterministic`、
`levelTower_input_eq`、`levelTower_agreement_lifts`。

---

## §10 走势分解 —— 17 课的完整形式

### 定义 10.1（规范 —— 分划 / 单调 / 类型齐次 / 唯一）

**叙述。** `decompose` 函数（定义 6.4）由四个性质约束：(1) 分划 ——
走势平铺中枢列表；(2) 单调性 —— 走势边界严格串接；(3) 类型齐次 ——
每个走势有唯一非 mixed 类型，且每个内部步骤一致；(4) 规范唯一性 ——
任何在索引 0 处行为相同的头扩展函数都等于 `decompose`。

### 定理 10.2 —— 四个性质成立

**叙述。** 上述四个性质对 `decompose` 全部成立。

**形式。** 把 §6 重述为形式化的「走势分解定理」：

    decompose_partition           : Σ walkSize = centers.length.
    decompose_monotonic           : w₁.end_ + 1 = w₂.start.
    decompose_type_homogeneous    : 每个走势的类型非 mixed 且内部齐次。
    decompose_spec_unique_extensional : 任何符合规范的函数 = decompose.

**Lean 证明。** 同 §6：`decompose_partition`、`decompose_monotonic`、
`decompose_type_homogeneous`、`decompose_unique`、
`decompose_spec_unique_extensional`、`decompose_spec_unique_empty`、
`decompose_spec_unique_head_at_zero`，辅以 `decomposeFrom_nonempty`。

---

## §11 区间套 —— 65/66 课（多分辨率）

### 定义 11.1（合成塔行走器）

**叙述。** `LevelWindow` 是一层上的连续索引区间。区间套行走器使用
`descend` 预言下沉穿过层次，预言提出一个更细的子窗口。当下沉停止时，
行走器以一个命名判定终止。

**形式。**

    LevelWindow := { level : ℕ, start : ℕ, end_ : ℕ }
    DescendValid descend := ∀ w w', descend w = some w' → w'.level < w.level
    walk descend w := if descend w = some w' then walk descend w' else terminate w.

**Lean 实现。** `Chanlun.IntervalNesting.LevelWindow`、`walk`，位于
[`lean/Chanlun/IntervalNesting.lean`](lean/Chanlun/IntervalNesting.lean)。

### 定理 11.2 —— 终止、绝不静默、pin 单调

**叙述。** 给定一个合法的下沉预言（每次下沉严格下降层级），行走器
终止，返回命名判定，且每个下沉的窗口的层级严格低于其父。成功下沉链
在每一步都严格下降层级。

**形式。**

    intervalnesting_terminates       : 在 DescendValid descend 下行走器总是停止.
    walk_always_has_verdict          : 每个输出状态都有命名判定.
    intervalnesting_pin_monotone     : descend w = some w' → w'.level < w.level.
    intervalnesting_chain_strict_drop: ∀ chain, 层级严格下降.

**Lean 证明。** `intervalnesting_terminates`、`walk_always_has_verdict`、
`intervalnesting_pin_monotone`、`intervalnesting_chain_strict_drop`。

### 定理 11.3 —— 终态形式

**叙述。** 在层 0 且无进一步下沉时，行走器返回 gate-limit 判定；
在正层且无进一步下沉时，返回 pinned 判定。

**形式。**

    walk_at_zero_returns_gate_limit
    walk_at_positive_returns_pinned.

**Lean 证明。** 同名定理位于 `Chanlun.IntervalNesting`。

### 状态 —— 多分辨率真实数据 grounding

**叙述。** 单分辨率合成塔行走器在 Lean 中完全证明。真正的多分辨率
主张 —— 下沉对应于切换到真实市场数据的更细时间周期，跨层用时间戳
对应 —— 用经验数据而非 Lean 解决。在 7 年 NQ 数据的 1d、1h、1m 三个
分辨率上，下沉成立：一个 1d 层中枢按时间戳映射到 1h 层时，包含
1h 层子中枢，进一步下沉到 1m。一些 1d 中枢在其时间戳跨度内没有 1h
子中枢 —— 这些是「本资金最低级」剩余，作为命名见证报告。

两个命名开放项是 `[chanlun_intervalnesting_multiscale_OPEN]` 与
`[chanlun_intervalnesting_lowest_level_OPEN]`，经验性地由
[`grounding/chanlun_multiscale_real_grounding.py`](grounding/chanlun_multiscale_real_grounding.py)
解决；Lean 提升需要一个真实时间戳映射模型，超出整数算术内核的范围。

---

## §12 MACD 辅助 measure（27 课，经验性 grounding）

**叙述。** 27 课与 disp/slope 并列地调用 MACD 作为显式辅助 measure。
grounding 解决两个经验性主张：

1. 在 7 年实盘 NQ 1h 数据上提取的 (A, C) 背驰窗口上，MACD 的判定与
   disp 在约 46.4%、与 slope 在约 17.9% 的窗口上一致 —— MACD 是
   再加工，不是替代。不一致位置以显式 (a_idx, c_idx, disp_says,
   macd_says) 见证发射。
2. 一个错误周期的 MACD（fast EMA 周期 9 而非 12）在同一输入上必然
   与规范 MACD 分歧 —— 参数选择是承重的。

**Lean 状态。** 命名开放为
`[chanlun_beichi_macd_measure_lean_OPEN]`。把
`Chanlun.Beichi.Measure` 扩展到第三个构造器在结构上是干净的；
障碍在于需要真实 MACD 能量值，整数算术内核无法在不引入单独数据接口
的情况下表达。

**脚本。**
[`grounding/chanlun_macd_grounding.py`](grounding/chanlun_macd_grounding.py)。

---

## §X 完整覆盖审计 —— 按类别的逐项状态

本节是原文 ↔ Lean 覆盖的结构性审计。原文的每一条命名条目 —— 定义或
定理 —— 都被归入四个相互排斥的类别之一，每条状态给出可外部审计的具体
理由。

### §X.0 状态图例与总数

#### 多解的两类

关于 MULTI_VALUED_NAMED 项目，一个自然的疑问是：「多解属于 open-world
问题是么？那是不是在输入新数据后，达到某个条件就坍塌为单解？」诚实
的回答是：本文档中的多解性其实**分为两类**，只有第一类承认坍塌。

- **类 A —— 可坍塌。** 多解性来自原文 UNDER-SPECIFY 的 IMPLEMENTATION
  DETAIL（严格还是弱不等号、zone 固定还是 re-tightening、从一个同向
  run 里挑哪个分型）。当输入满足一个具体的形式条件时，两种读法在
  每一步都重合。类 A 项目因此附带**坍塌定理**：一个 if-then 命题
  说「在性质 P 的输入上，读法 X = 读法 Y」。**满足 P 的新数据**会
  把歧义坍塌为单解；**违反 P 的新数据**让两种读法继续都合法。

- **类 B —— 永远多解（语义自由度）。** 多解性是原文真正留下的 OPEN
  CHOICE —— 一个 measure（disp vs slope vs MACD）、一个 oracle（哪个
  中枢提供参考）、一个理论刻意留给从业者的建模承诺。类 B 项目在新
  数据上**不**坍塌：这扇门问的是「该回答哪个问题」，K 线再多也不能
  裁定交易员问的是哪个问题。类 B 项目附带一个构造性歧义见证作为
  「不会坍塌」的证据（在合成数据 AND 经验数据上分歧都持续存在），
  再加一段**「为何不坍塌」**说明结构性原因。

六条 MULTI_VALUED_NAMED 项目分为 **3 条类 A**（X.3.7、X.5.10、X.5.11
—— 实现细节兄弟，都附带坍塌定理）与 **3 条类 B**（X.7.5、X.7.8、
X.8.3 —— disp-vs-slope measure 选择及其下游传递，都附带「为何不
坍塌」说明）。类标记是每条四段式条目承重内容。

#### 四类相互排斥的状态

四类相互排斥：

- **PROVEN_DIRECT.** `lean/Chanlun/` 下存在一条 sorry-free Lean 定理
  作为形式陈述。给出 Lean 标识符与一句证明技术摘要。
- **PROVEN_FIXTURE.** 通过具体固件上的计算证明（典型用 `native_decide`
  在固定具体实例上），不是 universal 陈述。
- **MULTI_VALUED_NAMED.** 原文真正允许多种读法；歧义由 Lean 构造性
  见证（位于 `Chanlun.DivergenceWitnesses` 或源模块）固定。**这不是
  缺失证明 —— 是一种被记录的多解性。**
- **NOT_FORMALIZED.** 尚无 Lean 定理。本格列出具体阻塞 —— 整数算术
  内核的具体限制、prelude-only 与 mathlib 边界、原文真正的歧义、
  或结构性的设计选择 —— 供外部读者核查。

**§X.1 – §X.10 总数**（1 项 = 1 行）：

| 状态 | 数量 | 说明 |
|---|---|---|
| PROVEN_DIRECT | 72 | sorry-free Lean 定理位于 `lean/Chanlun/`（包含历次 PR 形式化的 X.5.13 + X.9.6，以及 round-1 PR 通过 `Chanlun.OpenQuestionsAdvance` 新形式化的 X.5.12 + X.6.9 + X.8.8 + X.8.9 + X.9.7 + X.10.7，加上本轮 round-2 PR 通过 `Chanlun.OpenQuestionsAdvanceR2` 新形式化的 X.4.6 + X.7.9 + X.10.4 + X.10.5 + X.10.6） |
| MULTI_VALUED_NAMED | 6 | 每条都由 `Chanlun.DivergenceWitnesses` 或源模块中的构造性歧义见证支撑 |
| PROVEN_FIXTURE | 0 | （chanlun.md 本身中不计；经验性 grounding 位于 `grounding/` 与 `conformance/` 之下，不作为 Lean 陈述；多分辨率主张 X.10.4 引用 `grounding/chanlun_multiscale_real_grounding.py` 为 Lean 之外的 PROVEN_FIXTURE —— 与本轮 Lean 结构化形式互补） |
| NOT_FORMALIZED | 0 | round-2 闭合：原 §Y 全部五条经结构性载体（预言唯一性、MACD 扩展 Measure、TimestampWindow + 二分下降）提升为 PROVEN_DIRECT。详见 §Y 四段式处理，已交叉引用新增定理 |
| **合计** | **78** | 被审计的原文命名条目 |

六条 MULTI_VALUED_NAMED 是 X.3.7（任意输入上的笔 to 端点读法）、
X.5.10（zone-gate first3 vs all_）、X.5.11（贴边 ≤ vs <）、X.7.5
（disp vs slope）、X.7.8（盘整 disp vs slope + intra vs inter）、
X.8.3（measure-gate 传递到第一/第二买卖点）。本轮 round-2 PR 之后已
没有 NOT_FORMALIZED 余留：X.4.6（相对化 Φ 预言唯一性）、X.7.9（MACD
的 `MeasureExt.macd` 扩展构造子）、X.10.4（`TimestampWindow` 二分下降
—— 终止 + 严格子集）、X.10.5（按 span 强归纳的最低层见证存在性）、
X.10.6（MACD-filtered 时间戳下降）均已在
`Chanlun.OpenQuestionsAdvanceR2` 中给出 sorry-free 形式化。详见 §Y 段
四段式处理与对应交叉引用。

**本 PR 新形式化（NOT_FORMALIZED → PROVEN_DIRECT）**，全部位于
`Chanlun.OpenQuestionsAdvance` 模块：

* X.5.12（`all_` gate 下的扩展传播，列表归纳形式）：
  `applyEvents_no_rebirth_preserves_core`。`extension_preserves_core_ZD_ZG`
  的 gate-agnostic 列表归纳提升。
* X.6.9（mixed 合并下游步骤）：`mergeAdjacent`、`mixedMerge`、
  `mergeAdjacent_size_preserved` —— 成对合并器保持 `walkSize` 之和。
* X.8.8（第一/第二类买卖点的递归次级形式）：适配器
  `firstSecondToOptionBool` 加 `firstSecond_recursive_total`、
  `firstSecond_recursive_terminates`、`firstSecond_recursive_inheritance`
  —— 复用 §8.7 已用的 `recursiveSubBsp` fuel-bounded 下降。
* X.8.9（盘整背驰的递归次级形式）：适配器 `panzhengToOptionBool` 加
  `panzheng_recursive_total`、`panzheng_recursive_terminates`、
  `panzheng_recursive_inheritance`。
* X.9.7（级别递归的严格子窗口）：`subWindow` 加
  `subWindow_level_drops`、`subWindow_span_strict_drop`、
  `subWindow_startIdx_strict`、`subWindow_endIdx_strict`、
  `subWindow_descend_valid` —— 把 `LevelRecursion` 桥到
  `IntervalNesting.walk` 的 `DescendValid` 契约。
* X.10.7（走势分解 × 区间套整合）：`projectToWindow`、`walkInWindow`
  加 `projectToWindow_length_le`、`walkInWindow_partition`、
  `walkInWindow_size_le_span` —— 把 `List Center` 投影到窗口索引子区间。

**历次 PR 形式化（仍为 PROVEN_DIRECT）：**

* X.5.13 —— `Chanlun.LevelRecursion.listEnvelope_widens` +
  `listEnvelope_DD_drops` + `listEnvelope_GG_grows`。
* X.9.6 —— `Chanlun.LevelRecursion.liftOption` + `liftOption_eq_none_iff`
  + `liftOption_eq_some_iff` + `liftOption_strict_drop`。

**本 PR 新增的类 A 坍塌定理**（放在 `Chanlun.CollapseTheorems`）：

* X.5.10 坍塌：`zhongshu_zone_gate_collapses_when_no_tightening` ——
  当每个被接纳的元素都 CONTAIN first3 zone 时，`first3` 与 `all_`
  返回相同的 `extendEnd` 索引。
* X.5.11 坍塌：`zhongshu_shoulder_collapses_off_boundary`（及列表
  层提升 `_list`）—— 没有元素贴在 `e.lo = zg` 或 `e.hi = zd` 边界上
  时，≤ 与严格 < 两种重叠谓词读法一致。

X.3.7 坍塌定理
`Chanlun.BiEndpointSubResidues.to_endpoint_leftmost_eq_extremal_on_reachable`
原本就存在；本 PR 只补上分类标注。

### §X.1  算法 N（§1）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.1.1 | 定义 1.1 包含关系 | PROVEN_DIRECT | `Chanlun.Normalize.contained` + `noAdjContainment` |
| X.1.2 | 定义 1.2 单次扫描 normalize | PROVEN_DIRECT | `Chanlun.Normalize.normalize`（函数即定义） |
| X.1.3 | 定理 1.3 单次扫描产生 noAdjContainment | PROVEN_DIRECT | `Chanlun.Normalize.normalize_no_adjacent_containment`，对 `pushOne_preserves` 归纳 |

### §X.2  分型（§2）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.2.1 | 定义 2.1 顶/底分型 | PROVEN_DIRECT | `Chanlun.Fractal.classifyDef3` |
| X.2.2 | 定理 2.2 三分性 | PROVEN_DIRECT | `Chanlun.Fractal.def3_trichotomy`，对严格比较案例分析 |
| X.2.3 | 定理 2.3 叙述端 ↔ 算子端等价 | PROVEN_DIRECT | `Chanlun.Fractal.fractal_slot_equiv_def3`，9 路案例 |
| X.2.4 | 定理 2.4 管线组合 | PROVEN_DIRECT | `Chanlun.Pipeline.pipeline_inclusion_normalized`，经 `not_contained_iff_bar` |
| X.2.5 | 定理 2.5 良定义分类 | PROVEN_DIRECT | `Chanlun.Pipeline.pipeline_fractal_classification_well_defined` |
| X.2.6 | 端到端桥接（原始 Interval → 交替 fractalKinds） | PROVEN_DIRECT | `Chanlun.BiReachableDeterminismBridge.normalize_then_fractals_alternate` —— 一步组合 `normalize` + `map toBar` + `fractalKinds` → `AlternateKinds` |

### §X.3  笔（§3）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.3.1 | 定义 3.1 最左贪心笔构造 | PROVEN_DIRECT | `Chanlun.Stroke.step`、`Chanlun.Stroke.strokes` |
| X.3.2 | 定理 3.2 分隔（性质 B） | PROVEN_DIRECT | `Chanlun.Stroke.stroke_emits_separated`，经 `List.mem_reverse` 提升为 `strokes_separated` |
| X.3.3 | 定理 3.3 交替（性质 A） | PROVEN_DIRECT | `Chanlun.Stroke.stroke_emits_alternate`，反向输出提升 `Chanlun.BiEndpointSubResidues.strokes_alternate`，经 `allAlternate_reverse` |
| X.3.4 | 定理 3.4 strokes_unique（引理 2 强形式） | PROVEN_DIRECT | `Chanlun.StrokeUniqueness.strokes_unique`，对 `fold_consumes_alt` 不变量归纳 |
| X.3.4-推论 | IsValidBi 非空 + 双向版本 | PROVEN_DIRECT | `Chanlun.StrokesIsValidBiCorollary.strokes_isValidBi` 与 `strokes_iff_IsValidBi` |
| X.3.5 | 定理 3.5 端点子结果 (a)+(b)+(c) | PROVEN_DIRECT | `to_endpoint_leftmost_eq_extremal_on_reachable`、`dropBranch_step_no_op`、`dropBranch_preserves_IsValidBi`、`allAlternate_reverse`，位于 `Chanlun.BiEndpointSubResidues` |
| X.3.6 | 定理 3.6 可达域交替 | PROVEN_DIRECT | `Chanlun.BiReachableDeterminism.fractals_alternate_on_containment_free`，经 `dichotomy_of_no_containment` + `neither_preserves_direction` |
| X.3.7 | 任意输入上的 TO 端点读法（最左 admissible vs 极值字面） | MULTI_VALUED_NAMED → 可达域上 PROVEN_DIRECT | **类 A**（可坍塌）。见四段式定理 3.7。坍塌条件：严格交替的分型序列（`normalize` 的输出）。坍塌定理：`to_endpoint_leftmost_eq_extremal_on_reachable`（`Chanlun.BiEndpointSubResidues`），与可达域交替（定理 3.6）组合。任意输入上两种读法都合法；`StrokeUniqueness` 取最左 admissible 读法 |
| X.3.8 | 过近反向分型的静默丢弃 | PROVEN_DIRECT | `Chanlun.BiEndpointSubResidues.dropBranch_step_no_op` 证明丢弃分支是 no-op |

### §X.4  线段（§4）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.4.1 | 定义 4.1 BoundedFix 递归 | PROVEN_DIRECT | `Chanlun.Segment.segments`，参数化在 `find_term` + `find_term_ge` 上 |
| X.4.2 | 定理 4.2 strict-advance 终止测度 | PROVEN_DIRECT | `Chanlun.Segment.segment_advance_strictly_increasing`，整数算术 |
| X.4.3 | 定理 4.3 分划（性质 P） | PROVEN_DIRECT | `Chanlun.Segment.segments_partition`，经 `segments_partitionFrom` |
| X.4.4 | 定理 4.4 终止（性质 T，长度有界） | PROVEN_DIRECT | `Chanlun.Segment.segments_terminate`，经 `segments_length_le` |
| X.4.5 | 定理 4.5 预言接口非空 | PROVEN_DIRECT | `Chanlun.Segment.find_term_contract_nonvacuous`（见证 `trivialFindTerm`） |
| X.4.6 | 原文定理 1：相对于固定 `ΦOverlapAdmissible P` 谱的参数化 Φ-唯一性 | PROVEN_DIRECT（round-2 PR 新形式化） | `Chanlun.OpenQuestionsAdvanceR2.ΦOverlapAdmissible` + `oracle_pointwise_unique` + `segments_oracle_unique`。原文主张被 `P`-相对化：任两个满足同一可纳谱 `P` 的预言逐点相等（函数化谱），因此产生相同的笔表。具体 `P`（lesson 65 vs 67 的读法选择）作为每次实例化的内核选择暴露，而非内核仲裁 |

### §X.5  中枢（§5）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.5.1 | 定义 5.1 中枢形成 | PROVEN_DIRECT | `Chanlun.Zhongshu.zhongshu` |
| X.5.2 | 定义 5.2 扩展函数 + ZoneGate | PROVEN_DIRECT | `Chanlun.Zhongshu.extendEnd`，在 `ZoneGate ∈ {first3, all_}` 上参数化 |
| X.5.3 | 定理 5.3 zhongshu_valid（ZD ≤ ZG） | PROVEN_DIRECT | `Chanlun.Zhongshu.zhongshu_valid` |
| X.5.4 | 定理 5.4 zhongshu_disjoint | PROVEN_DIRECT | `Chanlun.Zhongshu.zhongshu_disjoint`，经 `zhongshu_head_start_ge` |
| X.5.5 | 定理 5.5 extendEnd_ge（扩展终止测度） | PROVEN_DIRECT | `Chanlun.Zhongshu.extendEnd_ge` |
| X.5.6 | 定义 5.6 四向扩展分类器（延伸/扩展/新生/endNoRebirth + 升级） | PROVEN_DIRECT | `Chanlun.ZhongshuExtension.classifyExtension` |
| X.5.7 | 定理 5.7 classifyExtension_total | PROVEN_DIRECT | `Chanlun.ZhongshuExtension.classifyExtension_total` |
| X.5.8 | 定理 5.8 每个事件的核心 / 外包络承重性 | PROVEN_DIRECT | `extension_preserves_core_ZD_ZG`、`expansion_widens_GG_DD`、`rebirth_creates_disjoint_core` |
| X.5.9 | 定理 5.9 9 段升级触发 | PROVEN_DIRECT | `upgrade_trigger_iff_9_segments` + `upgrade_trigger_element_independent` |
| X.5.10 | 定理 5.10 zone-gate 歧义见证 | MULTI_VALUED_NAMED | **类 A**（可坍塌）。见四段式定理 5.10。歧义见证 `Chanlun.DivergenceWitnesses.zhongshu_zone_gate_divergence_witness`；两种门都产生 valid + disjoint 输出（`zhongshu_zone_gate_witness_valid_disjoint`）。坍塌条件：每个后续元素都 CONTAIN first3 zone（`(els.get k).lo ≤ zd ∧ (els.get k).hi ≥ zg`）。坍塌定理：`Chanlun.CollapseTheorems.zhongshu_zone_gate_collapses_when_no_tightening` |
| X.5.11 | 贴边情形（`next_el.lo = ZG` 或 `next_el.hi = ZD`）—— ≤ vs 严格 < | MULTI_VALUED_NAMED | **类 A**（可坍塌）。见四段式定理 5.11。原文同时支持 ≤ 与 < 读法（17 课第 3 行措辞 vs 17 课例题计算）；本仓库取 ≤ 为规范。坍塌条件：每个后续元素都不贴边（`(els.get k).lo ≠ zg ∧ (els.get k).hi ≠ zd`）。坍塌定理：`Chanlun.CollapseTheorems.zhongshu_shoulder_collapses_off_boundary`（及列表层提升 `_list`） |
| X.5.12 | `all_` gate 下的扩展传播（完整列表归纳形式） | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.OpenQuestionsAdvance.applyEvents_no_rebirth_preserves_core` —— `extension_preserves_core_ZD_ZG` 的 gate-agnostic 列表归纳提升。证明技术：对事件列表归纳，分类讨论五个 `ExtensionEvent` 构造器。配套引理 `applyEventCore_ext_preserves` 与 `applyEventCore_exp_preserves` |
| X.5.13 | 跨完整中枢的多元素外包络（列表归纳形式） | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.LevelRecursion.listEnvelope_widens` + `listEnvelope_DD_drops` + `listEnvelope_GG_grows` 把单步 `expansion_widens_GG_DD` 提升为完整列表归纳形式：在任意后续元素列表上，累计 `DD` 弱下降，累计 `GG` 弱上升。证明技术：对后续元素列表归纳，每步使用 mathlib 的 `min_le_left` 与 `le_max_left` |

### §X.6  走势类型 + 分解（§6、§10）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.6.1 | 定义 6.1 stepDir + classify（WalkType） | PROVEN_DIRECT | `Chanlun.TrendType.stepDir`、`classify` |
| X.6.2 | 定理 6.2 classify_total | PROVEN_DIRECT | `Chanlun.TrendType.classify_total` |
| X.6.3 | 定理 6.3 趋势标签强制同向 | PROVEN_DIRECT | `Chanlun.TrendType.classify_trend_monotone`，经双向辅助 |
| X.6.4 | 定义 6.4 走势分解函数 | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose`（含 `extendRun` 辅助） |
| X.6.5 | 定理 6.5 decompose_partition | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_partition` |
| X.6.6 | 定理 6.6 decompose_monotonic（边界串接） | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_monotonic`，经 `decomposeFrom_chain` |
| X.6.7 | 定理 6.7 decompose_type_homogeneous | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_type_homogeneous` |
| X.6.8 | 定理 6.8 规范唯一性（外延） | PROVEN_DIRECT | `Chanlun.WalkDecomposition.decompose_spec_unique_extensional`，加 `decompose_spec_unique_empty` 与 `decompose_spec_unique_head_at_zero` |
| X.6.9 | `mixed` 合并下游步骤 | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.OpenQuestionsAdvance.mergeAdjacent` + `mixedMerge` 定义把相邻 trend_up/trend_down 对合并为 `mixed` 超级走势的成对合并器。`mergeAdjacent_size_preserved` 证明合并后 `walkSize` 等于两输入走势之和（在串接输入上）—— 合并步骤保持分划性质 |

### §X.7  背驰（§7、§12）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.7.1 | 定义 7.1 Move、位移、lhsRhs | PROVEN_DIRECT | `Chanlun.Beichi.Move`、`disp`、`lhsRhs` |
| X.7.2 | 定义 7.2 classifyBeichi | PROVEN_DIRECT | `Chanlun.Beichi.classifyBeichi` |
| X.7.3 | 定理 7.3 total + 反身性 | PROVEN_DIRECT | `classifyBeichi_total`、`beichi_irrefl`（经 `lhsRhs_self_eq`） |
| X.7.4 | 定理 7.4 承重（disp + slope 两侧） | PROVEN_DIRECT | `beichi_load_bearing_disp`、`beichi_load_bearing_slope`，合并 `beichi_load_bearing`；配套 `no_beichi_*_strict`、`tie_*_iff` |
| X.7.5 | 定理 7.5 disp-vs-slope 多解性 | MULTI_VALUED_NAMED | **类 B**（永远多解 —— 语义 measure 选择）。见四段式定理 7.5。歧义见证 `Chanlun.Beichi.beichi_measure_gate_witness`，提升为 `Chanlun.DivergenceWitnesses.beichi_measure_gate_divergence_witness`。原文在不同章节调用两个 measure（24 课 vs 27 课）。为何不坍塌：disp 与 slope 回答不同问题（距离 vs 速度），新数据不能裁定交易员问的是哪个。Python 参考上经验一致率约 82.2% 只量化分歧区域大小，不裁定胜者 |
| X.7.6 | 定义 7.6 盘整背驰分类器 | PROVEN_DIRECT | `Chanlun.PanzhengBeichi.classifyPanzheng` |
| X.7.7 | 定理 7.7 盘整 total + 承重 + incomplete-iff | PROVEN_DIRECT | `classify_panzheng_total`、`panzheng_load_bearing_disp`、`panzheng_load_bearing_slope`、`panzheng_incomplete_iff` |
| X.7.8 | 定理 7.8 盘整 measure-gate 见证 + intra-vs-inter 变种 | MULTI_VALUED_NAMED | **类 B**（永远多解 —— 继承 §7.5 measure 选择，再叠加第二个不可化归的「哪个中枢提供参考」oracle）。见四段式定理 7.8。歧义见证 `panzheng_measure_gate_witness`、`panzheng_intra_vs_inter_load_bearing`，提升为 `panzheng_measure_gate_propagation_witness`。为何不坍塌：intra-vs-inter 是「强度衰减相对于什么」的建模承诺，不是被更多数据收敛的估计 |
| X.7.9 | 把 MACD 作为扩展 Measure 的第三个构造器（与 disp/slope 并列） | PROVEN_DIRECT（round-2 PR 新形式化） | `Chanlun.OpenQuestionsAdvanceR2.MeasureExt` 扩展 `Chanlun.Beichi.Measure` 增设 `macd` 构造器；`lhsRhsExt`、`classifyBeichiExt`、`beichi_macd_load_bearing` 以抽象 `macdEnergy : Move → ℝ` 字段（使用 mathlib `Real`）镜像 disp/slope 形态。结构性载力性 —— `.macd` 下的 `beichi` ⇔ `macdEnergy c < macdEnergy a` —— 与能量实现选择无关。`MeasureExt.toBase` 是回到基 Measure 的遗忘映射 |

### §X.8  三类买卖点（§8）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.8.1 | 定义 8.1 第一/第二类分类器 | PROVEN_DIRECT | `Chanlun.FirstSecondBuysell.classifyBsp` |
| X.8.2 | 定理 8.2 total + 非破首点 | PROVEN_DIRECT | `classify_total`、`classify_first_point_only_total`、`second_buy_non_breaking`、`second_sell_non_breaking`、`second_not_breaking_iff`、`first_point_failed_iff` |
| X.8.3 | 定理 8.3 measure-gate 传递到第一/第二买卖点 | MULTI_VALUED_NAMED | **类 B**（永远多解，继承 §7.5 measure 选择的下游传递）。见四段式定理 8.3。歧义见证 `first_second_inheritance_load_bearing`，提升为 `Chanlun.DivergenceWitnesses.first_second_measure_gate_divergence_witness`。为何不坍塌：分类器结构上调用 `classifyBeichi`，内层是类 B，外层就继承同一个不可化归的 measure 选择 |
| X.8.4 | 定理 8.4 分类蕴含背景背驰 + pull 有定义 | PROVEN_DIRECT | `classify_implies_beichi_and_pull` |
| X.8.5 | 定义 8.5 第三类分类器 | PROVEN_DIRECT | `Chanlun.ThirdBuysell.classifyBsp` |
| X.8.6 | 定理 8.6 第三类 total + zone 承重 | PROVEN_DIRECT | `classifyBsp_total`、`bsp_zone_load_bearing_up`、`bsp_zone_load_bearing_down` |
| X.8.7 | 定理 8.7 第三类的递归次级形式 | PROVEN_DIRECT | `Chanlun.RecursiveSubBspBeichi.recursive_subBsp_total`、`recursive_subBsp_terminates`、`recursive_subBsp_inheritance`、`recursive_subBsp_fuel_stationary`、`recursive_subBsp_fuel_bound_via_levelRecursion` |
| X.8.8 | 第一/第二类买卖点的递归次级形式（与 §8.7 共享多级别下降测度） | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.OpenQuestionsAdvance.firstSecondToOptionBool` —— 从 `(TerminalWindow, Measure)` 到 `Option Bool` 的适配器。配套定理 `firstSecond_recursive_total`、`firstSecond_recursive_terminates`、`firstSecond_recursive_inheritance` 把 §8.7 的 `recursiveSubBsp` total / 终止 / 继承传递到第一/第二类载体 |
| X.8.9 | 盘整背驰（37 课）的递归形式 | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.OpenQuestionsAdvance.panzhengToOptionBool` —— 从 `(PanzhengTriple, Measure)` 到 `Option Bool` 的适配器。配套定理 `panzheng_recursive_total`、`panzheng_recursive_terminates`、`panzheng_recursive_inheritance` 把 §8.7 的 `recursiveSubBsp` total / 终止 / 继承传递到盘整载体 |

### §X.9  级别递归（§9）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.9.1 | 定义 9.1 centerSize + 级别提升 | PROVEN_DIRECT | `Chanlun.LevelRecursion.centerSize`、`liftCenter`、`liftCenters`、`liftStep`、`levelTower` |
| X.9.2 | 定理 9.2 lift_strict_drop（「走势必完美」） | PROVEN_DIRECT | `Chanlun.LevelRecursion.lift_strict_drop` + `level_recursion_count_decreases`，经 `centerSize_ge_3` + `total_size_ge_3_times_count` |
| X.9.3 | 定理 9.3 centerSize ≥ 3 | PROVEN_DIRECT | `Chanlun.LevelRecursion.centerSize_ge_3`，`extendEnd_ge` 的直接推论 |
| X.9.4 | 定理 9.4 外包络承重（lifted Element 有 lo ≤ hi） | PROVEN_DIRECT | `liftCenter_range_eq_core`、`liftCenter_lo_le_hi`、`liftCenters_all_valid`、`liftCenters_mem_iff` |
| X.9.5 | 定理 9.5 跨层级的确定性保持 | PROVEN_DIRECT | `liftStep_deterministic`、`levelTower_deterministic`、`levelTower_input_eq`、`levelTower_agreement_lifts` |
| X.9.6 | total 的 `lift : List Element → Option (List Element)` 偏函数包装器 | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.LevelRecursion.liftOption` 在终态输入（无中枢形成）时返回 `none`，在非终态时返回 `some next`；配套定理 `liftOption_eq_none_iff`、`liftOption_eq_some_iff`、`liftOption_strict_drop` 描述两个分支并在 `some` 分支上重新派生严格下降。严格下降测度（定理 9.2）是承重内容；本 PR 加的是 Option 包装以便迭代 |
| X.9.7 | 级别递归的严格子窗口（层-(n−1) 子窗口是层-(n−1) 塔的严格子集） | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.OpenQuestionsAdvance.subWindow` 在层 n − 1 上取严格内部子窗口。配套定理 `subWindow_level_drops`、`subWindow_span_strict_drop`、`subWindow_startIdx_strict`、`subWindow_endIdx_strict` 证明严格子集结构。`subWindow_descend_valid` 证明选择器满足 `IntervalNesting.DescendValid` 契约 —— 把 `LevelRecursion` 桥到 `IntervalNesting.walk` |

### §X.10  区间套（§11）

| # | 条目 | 状态 | 引用 / 阻塞 |
|---|---|---|---|
| X.10.1 | 定义 11.1 合成塔行走器 | PROVEN_DIRECT | `Chanlun.IntervalNesting.LevelWindow`、`walk`、`DescendValid` |
| X.10.2 | 定理 11.2 终止 + 绝不静默 + pin-monotone + chain-strict-drop | PROVEN_DIRECT | `intervalnesting_terminates`、`walk_always_has_verdict`、`intervalnesting_pin_monotone`、`intervalnesting_chain_strict_drop` |
| X.10.3 | 定理 11.3 终态形式 | PROVEN_DIRECT | `walk_at_zero_returns_gate_limit`、`walk_at_positive_returns_pinned` |
| X.10.4 | 多分辨率（时间戳映射）组合的结构形式：在 `TimestampWindow` 上的二分下降 | PROVEN_DIRECT（round-2 PR 新形式化） | `Chanlun.OpenQuestionsAdvanceR2.TimestampWindow` + `descendTimestamps`；配套定理 `descendTimestamps_level_drops`、`descendTimestamps_span_strict_drop`、`descendTimestamps_start_eq`、`descendTimestamps_end_strict`；打包于 `timestamp_walk_terminates` 与 `timestamp_walk_strict_subset_per_level`。通过 `descendTimestampsAsLevel_descend_valid` 桥接到 `IntervalNesting.DescendValid`。`Timestamp := ℕ`（离散 tick 网格）；wall-clock 语义是内核之上的解释层 |
| X.10.5 | 「本资金最低层」剩余的刻画 | PROVEN_DIRECT（round-2 PR 新形式化） | `Chanlun.OpenQuestionsAdvanceR2.IsLowestForFlow` + `lowest_level_witness_exists`。对窗口 span 强归纳（Nat 良基）构造 `descendTimestamps` 返回 `none` 的 `tw_low` —— 时间戳下降的结构性下界 |
| X.10.6 | MACD 装饰的区间套变体 | PROVEN_DIRECT（round-2 PR 新形式化） | `Chanlun.OpenQuestionsAdvanceR2.descendMacdFiltered` 把 §Y.2 的 MACD 一致谱与 §Y.3 的时间戳下降复合；`descendMacdFiltered_level_drops`、`descendMacdFiltered_span_strict_drop`、`macd_filtered_walk_terminates`、`descendMacdFiltered_refines_descendTimestamps` 打包终止 + refinement（过滤下降是原始下降的子函数） |
| X.10.7 | 走势分解 × 区间套整合 | PROVEN_DIRECT（本 PR 新形式化） | `Chanlun.OpenQuestionsAdvance.projectToWindow` 把 `List Center` 投影到 `LevelWindow` 索引子区间；`walkInWindow` 在投影上运行 `decompose`。配套定理 `projectToWindow_length_le`、`walkInWindow_partition`、`walkInWindow_size_le_span` 证明分划性质在投影下保持：窗口内 `walkSize` 之和由窗口索引跨度作上界 |

---

## §Y 开放问题

本节原先集中收纳 round-1 PR（#17）后仍处于 NOT_FORMALIZED 的五条
原文命名条目。round-2 PR（`Chanlun.OpenQuestionsAdvanceR2`）通过引入
结构性载体（mathlib 的 `Real`、`ℕ` 上的 `TimestampWindow`、MACD 扩展的
`MeasureExt`）已**把全部五条都提升到 PROVEN_DIRECT**。原先的
「kernel-limit」阻塞理由过于保守：§Y.2–§Y.5 的原文主张是**结构性**的
（终止、单调性、过滤），并不依赖任何具体 MACD 浮点 EMA 数值。具体
运行时数据语义仍位于 `grounding/` 脚本中，作为 Lean 之外的 PROVEN_FIXTURE。

每条记录：(i) 原始散文主张；(ii) 形式目标；(iii) round-2 完成的 Lean 闭合。

### §Y.1 原文定理 1 —— 参数化 Φ-唯一性（X.4.6）

**散文。** 原文定理 1 说：线段分解是「所有 valid 特征序列（Φ）+
重叠 admissibility 预言」这一参数化类的唯一分解。任何两个满足
**同一可纳谱**的预言在每个输入上产生相同的线段列表。

**形式目标。**

    ∀ (P : ℕ → ℕ → Prop) (f₁ f₂ : ℕ → Option ℕ),
      ΦOverlapAdmissible P f₁ →
      ΦOverlapAdmissible P f₂ →
      ∀ n a, segments f₁ _ n a = segments f₂ _ n a.

**Lean 闭合（round 2）。** `Chanlun.OpenQuestionsAdvanceR2`：

* `ΦOverlapAdmissible P f := ∀ a j, f a = some j ↔ P a j` —— 谱
  由单一可纳谓词 `P` 参数化。`P` 固定后预言函数化确定。
* `oracle_pointwise_unique` —— 满足同一 `P` 的任两个预言逐点相等。
* `segments_oracle_unique` —— 逐点相等加上 `find_term_ge` 假设的
  证据无关性提升到线段表的外延相等。

「65 课 vs 67 课」分歧本身是 `P` 的**选择**；内核暴露此选择而非仲裁。
`P` 固定后预言唯一性即为一个 Lean 定理。

### §Y.2 Beichi 的 MACD measure 构造器（X.7.9）

**散文。** 27 课引入 MACD 能量作为 disp 与 slope 之外的辅助 力度 measure。

**形式目标。**

    inductive MeasureExt | disp | slope | macd
    def lhsRhsExt (a c : Move) : MeasureExt → (ℝ × ℝ)
    def classifyBeichiExt (a c : Move) (m : MeasureExt) : BeichiVerdict
    theorem beichi_macd_load_bearing

**Lean 闭合（round 2）。** `Chanlun.OpenQuestionsAdvanceR2`：

* `MeasureExt` 扩展 `Chanlun.Beichi.Measure` 增设 `macd` 构造器；
  `MeasureExt.toBase` 是回到基 Measure 的遗忘映射（`.macd` 无基
  原像，证明 `MeasureExt` 真正更大）。
* `macdEnergy : Move → ℝ` 是抽象能量字段 —— 运行时数据接口提供的
  `Real` 读数。内核形式化不承诺具体 EMA 计算。
* `classifyBeichiExt` 在 `MeasureExt` 上镜像 disp/slope 形态；
  `classifyBeichiExt_total` 与 `classifyBeichiExt_irrefl` 延伸
  基的全性 / 反自身性定律。
* `beichi_macd_load_bearing` 证明结构性载力性：`.macd` 下的
  `beichi` ⇔ `macdEnergy c < macdEnergy a` —— 与能量实现选择无关。

### §Y.3 真实数据上的多分辨率时间戳组合（X.10.4）

**散文。** 65/66 课描述跨真实时间周期数据的 区间套 行走：1d → 1h → 1m
下沉，每个下层严格内嵌于上层窗口。

**形式目标。**

    structure TimestampWindow := (level : Nat) (t_start t_end : ℕ) (h_valid : t_start < t_end)
    def descendTimestamps : TimestampWindow → Option TimestampWindow
    theorem timestamp_walk_terminates
    theorem timestamp_walk_strict_subset_per_level

**Lean 闭合（round 2）。** `Chanlun.OpenQuestionsAdvanceR2`：

* `Timestamp := ℕ`（离散 tick 网格；wall-clock 语义是内核之上的
  解释层）。
* `TimestampWindow` 带证据 `h_valid : t_start < t_end`；
  `TimestampWindow.span` 为 tick 跨度。
* `descendTimestamps` 在中点 `(t_start + t_end) / 2` 处取左半段下降；
  在 `level = 0` 或 `t_end ≤ t_start + 1`（跨度 ≤ 1）时返回 `none`。
* `descendTimestamps_level_drops`、`descendTimestamps_span_strict_drop`、
  `descendTimestamps_start_eq`、`descendTimestamps_end_strict` ——
  每轴单调性定律。
* `timestamp_walk_terminates` 与 `timestamp_walk_strict_subset_per_level`
  打包结构性主张。
* `descendTimestampsAsLevel_descend_valid` 把下降桥接到
  `Chanlun.IntervalNesting.DescendValid`，使既有的区间套行走器能
  消费时间戳下降。

### §Y.4 本资金最低层剩余（X.10.5）

**散文。** 原文命名「本资金最低层」 —— 行走器仍能确认 背驰 的
最小层。

**形式目标。**

    theorem lowest_level_witness_exists :
      ∃ tw : TimestampWindow, IsLowestForFlow tw

**Lean 闭合（round 2）。** `Chanlun.OpenQuestionsAdvanceR2`：

* `IsLowestForFlow tw := descendTimestamps tw = none` —— 下降的
  结构性下界。
* `lowest_level_witness_exists` 由 `TimestampWindow.span` 强归纳
  证明（Nat 良基）：迭代 `descendTimestamps`；由 §Y.3 的严格下降律，
  span 最终触底使下降返回 `none`。

### §Y.5 MACD 装饰的区间套变体（X.10.6）

**散文。** 区间套 行走器与每一层 MACD 一致谱的复合过滤变体。

**形式目标。**

    def descendMacdFiltered : TimestampWindow → Option TimestampWindow
    theorem macd_filtered_walk_terminates

**Lean 闭合（round 2）。** `Chanlun.OpenQuestionsAdvanceR2`：

* `MacdAgrees : TimestampWindow → Prop`（可判定；抽象契约 ——
  运行时数据提供实际计算）。
* `descendMacdFiltered` 链接 `descendTimestamps` 与一致谱过滤。
* `descendMacdFiltered_level_drops`、
  `descendMacdFiltered_span_strict_drop` —— 继承的单调性定律
  （过滤只缩短链）。
* `macd_filtered_walk_terminates` —— 与 §Y.4 同样的 span 强归纳
  论证，外加过滤步骤。
* `descendMacdFiltered_refines_descendTimestamps` —— 过滤下降是
  原始下降的**子函数**（结构性 refinement）。

### §Y.6 闭合汇总（round 2）

round-2 PR（`Chanlun.OpenQuestionsAdvanceR2`）之后：

- **Kernel limits**：0 条（§Y.2–§Y.5 全部四条都由结构性载体闭合 ——
  MACD 能量用 `Real`、时间戳用 `ℕ`、下降用二分）。
- **Module bridging gaps**：0 条（round 1 已闭合）。
- **Paper genuine ambiguity**：0 条（§Y.1 通过 `P`-相对唯一性闭合；
  lesson-65/67 读法选择作为每次实例化的 `P` 暴露）。
- **Tooling limits**：0 条（mathlib 的 `Real` 已足够）。

round-2 PR 后 NOT_FORMALIZED 合计：**0 条**。PROVEN_DIRECT 合计：
**72 条**。诚实的范围声明：round-2 闭合形式化了 §Y.2–§Y.5 的**结构性**
内容（终止、单调性、过滤、层下降律）。具体 MACD EMA 计算的运行时数据
语义，或时间戳 tick 的 wall-clock 映射，仍是 `grounding/` 脚本中以
PROVEN_FIXTURE 形式存在的解释层关心。

---

## §A 致谢

缠论属于缠中说禅的传承。上述数学重述与 `lean/Chanlun/` 下的 Lean
编码是本仓库的贡献。其中非显然的贡献是：可达域交替定理（定理 3.6）、
lift 严格下降终止测度（定理 9.2）、以及 zone-gate 的构造性歧义见证
（定理 5.10）。其余都是已发表理论的 Lean 形式。

---

## §L 许可

形式化、本文档、参考实现脚本与 CI 工作流按 MIT 许可发布。如有
`LICENSE` 文件以其为准。
