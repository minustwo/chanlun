# 缠论 —— 理论 + Lean 形式化

**缠论**（缠中说禅老师所传授的技术分析理论）的内核验证 Lean 4 形式化，配套
一个可执行的纯 Python 参考实现和多语言移植。

* **理论文档**：[`chanlun.zh.md`](chanlun.zh.md)（数学形式）。
* **Lean 4 形式化**（`lean/Chanlun/`）：21 个模块，覆盖发表版流水线与
  结构/买卖点层。所有模块在 Hosted Ubuntu CI 上由 Lean 内核验证，
  无任何 `sorry`。
* **纯 Python 参考实现**（`grounding/`）：每个 Lean 定理都有独立 Python
  实现作为对照，并配有反例突变测试。
* **冻结的一致性语料库**（`conformance/chanlun-v1/`）：逐字节对齐、
  语言无关的测试套件。48 个 fixture × 6 个阶段，SHA-256 锁定。
* **多语言移植**（`impl/`）：TypeScript、Go、PineScript 后端均实现同一算法。

English version: see [README.md](README.md).

> **致谢声明**：缠论本身属于缠中说禅的传承。[`chanlun.zh.md`](chanlun.zh.md)
> 中的数学形式是本仓库对 Lean 库的叙述形式；`lean/Chanlun/` 下的 Lean
> 模块才是可信工件。

---

## TL;DR

缠论将价格序列确定性地分解为几何单位（分型 → 笔 → 线段 → 中枢 → 走势）。
本仓库 (a) 在 Lean 4 中形式化该分解，使主要正确性命题受机器检查；
(b) 提供一个可执行的参考实现，并把其输出以逐字节冻结的方式封装为
一致性语料库；(c) 把参考实现移植到 TypeScript、Go、PineScript。

* **已证**：21 个 Lean 模块，覆盖定义 3 与定义 4、算法 N（包含处理）、
  引理 2（笔唯一性）、定理 1（线段分解终止）、中枢构造、走势类型分类器、
  递归买卖点层。
* **未证**：详见下方「已知限制与待证问题」。每条限制都明示，而非隐藏。
* **从哪里读起**：理论 [`chanlun.zh.md`](chanlun.zh.md) → Lean 模块
  [`lean/Chanlun/`](lean/Chanlun/) → 一致性语料库
  [`conformance/chanlun-v1/`](conformance/chanlun-v1/)。

---

## 已证结果

Lean 库 `Chanlun`（`lake build Chanlun`）`sorry`-free，覆盖了发表版四段
流水线加上结构层（中枢 / 走势类型）、买卖点 / 背驰层、级别递归、区间套。
共 21 个模块：

### 核心流水线（Def-3 → 笔 → 线段 → 中枢）

| 模块 | 定理（chanlun.zh.md 索引） |
|---|---|
| `Chanlun.Fractal` | Def-3 分型：`fractal_slot_equiv_def3`、`def3_trichotomy`（引理 1）、`def3_admissible_classifies`、`def3_residue_iff_neither` |
| `Chanlun.Normalize` | 算法 N（包含处理，附录 A）：`normalize_no_adjacent_containment`（单次扫描 = 完全合并） |
| `Chanlun.Pipeline` | N → Def-3 组合：`pipeline_inclusion_normalized`、`pipeline_fractal_classification_well_defined` |
| `Chanlun.Stroke` | Def-4 笔（最左贪心）：`stroke_emits_separated`（B）、`stroke_emits_alternate`（A）、`strokes_separated` |
| `Chanlun.StrokeUniqueness` | 引理 2 强形式：`strokes_unique`（任何 `IsValidBi` = 流式输出的规范结果） |
| `Chanlun.StrokesIsValidBiCorollary` | 引理 2 非空 + 双向：`strokes_isValidBi`、`strokes_iff_IsValidBi` |
| `Chanlun.BiEndpointSubResidues` | 笔端点子结果：`to_endpoint_leftmost_eq_extremal_on_reachable`、`dropBranch_preserves_IsValidBi`、`allAlternate_reverse`、`strokes_alternate` |
| `Chanlun.Segment` | Def 5–16 + 定理 1（线段 + 参数化唯一段分解）：`segments_partition`（P）、`segments_terminate`（T）、`segment_advance_strictly_increasing` |
| `Chanlun.Zhongshu` | 中枢（17/20 课）：`zhongshu_valid`、`zhongshu_disjoint`、`extendEnd_ge`，参数化于 `ZoneGate ∈ {first3, all_}` |
| `Chanlun.ZhongshuExtension` | 中枢 延伸 / 扩展 / 新生 / 9-段升级（17/20/30 课）：`classifyExtension_total`、`extension_preserves_core_ZD_ZG`、`expansion_widens_GG_DD`、`rebirth_creates_disjoint_core`、`upgrade_trigger_iff_9_segments` |
| `Chanlun.TrendType` | 盘整 / 趋势（17 课）：`classify_total`、`classify_trend_monotone` |
| `Chanlun.WalkDecomposition` | 走势最大分解（17 课）：`decompose_partition`、`decompose_monotonic`、`decompose_type_homogeneous`、`decompose_unique` |

### 可达域确定性

| 模块 | 定理 |
|---|---|
| `Chanlun.BiReachableDeterminism` | 可达域确定性：`fractals_alternate_on_containment_free`（包含处理后 ⇒ 分型严格交替 ⇒ 三种笔端点读法在可达输入上完全重合） |
| `Chanlun.BiReachableDeterminismBridge` | Bar↔Interval 桥接：`map_toBar_preserves_noAdjContainment`、`normalize_then_fractals_alternate`（原始 `Interval` ⇒ 交替性一步到位） |

### 买卖点 + 背驰（20/24/27/29/37 课）

| 模块 | 定理 |
|---|---|
| `Chanlun.Beichi` | 背驰 力度 比较（24/27/29 课）：`classifyBeichi_total`、`beichi_irrefl`、`beichi_load_bearing`（位移 + 斜率 整数交叉乘积）、`beichi_measure_gate_witness` |
| `Chanlun.PanzhengBeichi` | 盘整背驰（37 课）：单中枢 A-vs-C 分类器：`classify_panzheng_total`、`panzheng_load_bearing_disp`/`slope`、`panzheng_measure_gate_witness`、`panzheng_intra_vs_inter_load_bearing` |
| `Chanlun.ThirdBuysell` | 第三类买卖点（20 课）：`classifyBsp_total`、`bsp_zone_load_bearing`、`bsp_reenter_up_iff`/`bsp_reenter_down_iff`、`bsp_excl` |
| `Chanlun.FirstSecondBuysell` | 第一/第二类买卖点（24 课）：`classify_total`、`classify_first_point_only_total`、`second_not_breaking_iff`、`first_point_failed_iff`、`first_second_inheritance_load_bearing` |
| `Chanlun.RecursiveSubBspBeichi` | 递归 三买卖 + 背驰（20/24/27/29 课推广至次级别）：`recursive_subBsp_fuel_stationary`、`recursive_subBsp_terminates`、`recursive_subBsp_inheritance`、`recursive_subBsp_total`、`recursive_subBsp_fuel_bound_via_levelRecursion` |

### 级别递归 + 区间套

| 模块 | 定理 |
|---|---|
| `Chanlun.LevelRecursion` | 走势必完美（24 课）：`centerSize_ge_3`、`lift_strict_drop`（每次非终端 lift 元素数严格下降 ≥2 ⇒ 级别递归在 ≤ n/2 步内终止） |
| `Chanlun.IntervalNesting` | 区间套（65–66 课）：`intervalnesting_terminates`、`walk_always_has_verdict`、`intervalnesting_pin_monotone`、`intervalnesting_chain_strict_drop`、`walk_at_zero_returns_gate_limit`、`walk_at_positive_returns_pinned` |

---

## 已知限制与待证问题

以下条目尚未在 Lean 库中证明。这里全部明示，使范围公开透明，而不是
将其隐藏。

* **包含归一前置桥接**。`Chanlun.Pipeline.pipeline_inclusion_normalized`
  卸载了 Def-3 上游假定的前置条件，但 `Interval` 层与 `Bar` 层之间的类型
  桥接显式命名，未折叠为一条定理。
* **线段递归内部细节**。`find_term` 的特征序列 Φ 与重叠 admissibility
  内部细节在 `Chanlun.Segment` 中没有重新推导；递归被参数化在
  「最左 ≥ a」的契约 `find_term_ge` 上。满足契约的 `find_term` 具体实例
  作为给定。
* **中枢 zone-gate 的非唯一性**。两种 zone-gate（`first3` 与 `all_`）
  在大约 12% 的任意元素序列上结果不同。两者都被证 `valid` + `disjoint`；
  这里 gate 相对性是缠论原文留待解释的真实多解性。在可达（无包含）域上，
  两种读法重合。
* **笔 to 端点的读法**。`Chanlun.StrokeUniqueness` 把 TO 端点读作最左
  的反向 admissible 分型；按「到端 run 的极值」字面强读可能在多分型 run
  上不同。在可达输入上两种读法重合（见 `Chanlun.BiReachableDeterminism`）。
* **过近反向分型的丢弃**。反向且过近（gap `< δmin`）的分型被 `step`
  静默丢弃；唯一性证明将丢弃视为 no-op。
* **反向输出顺序上的交替性**。`strokes_separated` 通过 `List.mem_reverse`
  提升到用户面向的反向顺序；反向顺序上的交替性是另一个一行 lemma，
  尚未包含。
* **级别递归的 `lift` 函数**。实际的
  `lift : List Element → Option (List Element)` 函数不在范围内；只证明了
  承载终止性的严格下降测度。
* **级别递归的 envelope 健全性**。每个第 `(n+1)` 层 envelope 包含其成员
  的范围；尚未证明。
* **级别递归的确定性传递**。确定性沿塔上提保持；尚未证明。
* **走势分解的 spec 唯一性**。任何满足走势分解规范的函数等于 `decompose`；
  尚未以 spec 形式证明。
* **中枢延伸的边界情形**。「贴边」（`next_el.lo = ZG` 或 `next_el.hi = ZD`）
  按 `≤`-overlap 读法归入延伸；严格 `<` 读法会归到新生边界。两种读法
  都在缠论原文中出现，本仓库取 `≤` 读法。
* **`all_` gate 上的中枢扩展**。`first3` 形式的扩展传播已在
  `Chanlun.ZhongshuExtension` 中关闭；`all_` 形式尚未。
* **跨完整中枢的多元素 envelope**。单步已证，列表归纳尚未完成。
* **背驰力度 measure**。位移（`disp`）与斜率在 Python 参考实现上一致率
  约 82.2%。`beichi_measure_gate_witness` 证明非空；measure 选择本身留作
  开放（这是缠论原文对力度比较未固定单一 measure 而留下的多解性）。
* **MACD 作为背驰 measure**。27 课引入 MACD 作为辅助力度 measure；
  明确视为非规范。
* **盘整背驰 measure 的跨突变传递**。盘整背驰 measure 在突变表上的
  传递性尚未证明。
* **第一/第二类买卖点与盘整背驰的递归形式**。24 课与 37 课的递归
  （多级别）形式共享同一 descent 测度 + measure-gate 继承；尚未证明。
* **级别递归的严格子窗口**。层-`(n-1)` 子窗口是层-`(n-1)` 塔的严格
  子集，尚未严格证明。
* **最低层 pin 端点与多尺度组合**。最低层 pin 端点的严格刻画，以及
  非相邻层之间嵌套区间的多尺度组合。
* **MACD 装饰的区间套变体**。
* **走势分解 × 区间套**。`Chanlun.WalkDecomposition` 接入
  `Chanlun.IntervalNesting`。

---

## 构建

### 前置依赖

* [`elan`](https://github.com/leanprover/elan)（Lean 工具链管理器）
* 固定的 Lean 版本（`leanprover/lean4:v4.14.0`，在 `lean-toolchain` 中设置）

### 构建 Lean 库

```bash
# 解析并下载依赖（Mathlib v4.14.0 + 传递性依赖）。
lake update
# 下载预构建的 Mathlib oleans（在免费 hosted runner 上可工作）。
lake exe cache get
# 构建 Chanlun 库。
lake build Chanlun
```

`lake build Chanlun` 成功 ⇒ 21 个模块在 Lean 内核下无任何 `sorry`。

### 运行参考实现

```bash
cd grounding
for f in chanlun_*_grounding.py; do
  echo "===== $f ====="
  PYTHONPATH=. python3 "$f"
done
```

每个参考实现几秒内跑完（60k–240k 随机序列），打印一行 OK 摘要加上
反例突变检查。无外部 Python 依赖；纯标准库 + `random`。

---

## 目录结构

```
chanlun/
├─ chanlun.md                         # 数学形式（英文）
├─ chanlun.zh.md                      # 数学形式（中文）
├─ README.md                          # 英文版
├─ README.zh.md                       # 本文件（中文）
├─ lakefile.lean, lean-toolchain      # Lean 4 构建配置（Mathlib v4.14.0）
├─ lean/Chanlun/                      # 21 个 Lean 模块
│  ├─ Fractal.lean, Normalize.lean, Pipeline.lean
│  ├─ Stroke.lean, StrokeUniqueness.lean, StrokesIsValidBiCorollary.lean
│  ├─ BiEndpointSubResidues.lean
│  ├─ Segment.lean
│  ├─ Zhongshu.lean, ZhongshuExtension.lean
│  ├─ TrendType.lean, WalkDecomposition.lean
│  ├─ BiReachableDeterminism.lean, BiReachableDeterminismBridge.lean
│  ├─ Beichi.lean, PanzhengBeichi.lean
│  ├─ ThirdBuysell.lean, FirstSecondBuysell.lean
│  ├─ LevelRecursion.lean, RecursiveSubBspBeichi.lean
│  ├─ IntervalNesting.lean
├─ grounding/                         # 纯 Python 参考实现
│  ├─ chanlun_inclusion_grounding.py
│  ├─ chanlun_singlepass_idempotent_grounding.py
│  ├─ chanlun_stroke_grounding.py
│  ├─ chanlun_trend_type_grounding.py
│  ├─ chanlun_zhongshu_grounding.py
│  ├─ chanlun_bi_endpoint_multivalued_grounding.py
│  └─ chanlun_bi_kline_rule_grounding.py
├─ conformance/chanlun-v1/             # 冻结的一致性语料库
│  ├─ manifest.json                    # corpus_sha256 = 版本号
│  ├─ fixtures/*.json                  # 48 个（输入、期望、sha）fixture
│  ├─ reference_backend/               # 独立纯标准库参考实现（Python）
│  ├─ runner.py                        # ~100 行纯标准库验证脚本
│  ├─ generate_corpus.py               # 确定性 fixture 生成器
│  ├─ example_phase3_check.py          # 下游实现的模板
│  ├─ README.md, README.zh.md          # 完整规范文档（英 / 中）
├─ impl/ts/                            # TypeScript 移植
│  ├─ src/*.ts                         # 六个流水线阶段，零运行时依赖
│  ├─ check.ts                         # 48-fixture 一致性验证脚本
│  ├─ package.json                     # 仅 devDeps（typescript + @types/node）
│  └─ README.md, README.zh.md
├─ impl/go/                            # Go（纯标准库）后端，通过全部 48 fixture
│  ├─ go.mod                           # github.com/minustwo/chanlun/impl/go, Go 1.22
│  ├─ cmd/check/main.go                # `go run ./cmd/check` 跑一致性 harness
│  ├─ internal/chanlun/                # 每个 stage 一个文件，忠实移植自 Python 参考
│  └─ README.md, README.zh.md
├─ impl/pinescript/                    # PineScript v5 文档化移植
│  ├─ chanlun_indicator.pine           # 指标本体（贴进 TradingView）
│  ├─ PINESCRIPT_PORT.md               # 分阶段映射 + 已命名限制
│  └─ README.md, README.zh.md
└─ .github/workflows/chanlun-gate.yml  # Hosted Ubuntu CI：lake build + 参考实现 + 一致性 + lint
```

### PineScript 后端 —— 仅文档化移植

`impl/pinescript/` 是同一算法的 PineScript v5 移植，会把 分型 / 笔 / 中枢
画在 TradingView 真实 K 线上。**它没有做一致性验证**：PineScript v5
无法在 CI 中读 fixture 语料或做 SHA-256 比对，所以每个验证缺口都在
`impl/pinescript/PINESCRIPT_PORT.md` 中显式列出。CI 跑一个**纪律检查**
（`conformance-pinescript-lint`）核对反模式不存在、限制都已记录 ——
但它**不是** SHA-equality 一致性 gate。

---

## CI

Hosted Ubuntu 工作流 `.github/workflows/chanlun-gate.yml` 在每次 push 到
`main` 和每个 PR 上运行：

* `lean` job：安装 `elan` + 固定工具链，恢复 `.lake` 的 `actions/cache@v4`
  缓存，跑 `lake exe cache get` 拉 Mathlib 预构建 oleans，然后
  `lake build Chanlun`。最后一关拒绝任何 `lean/Chanlun/*.lean` 中出现的
  `sorry` 关键字。
* `grounding` job：用纯标准库 Python 3.11 跑每个
  `grounding/chanlun_*_grounding.py`。
* `conformance` job：跑 `python3 conformance/chanlun-v1/runner.py`，验证
  每个 fixture 逐字节匹配冻结规范；接着重新生成语料库并确认字节完全
  相同（以捕获参考实现的任何漂移）。`chanlun-v1` 的 `corpus_sha256` 即为
  一致性版本号：任何语言的实现要合规，必须重现每个 fixture 的期望
  SHA-256。
* `conformance-ts` job：安装 Node 20、编译 `impl/ts/`（仅 devDeps：
  `typescript` + `@types/node`）、运行 `impl/ts/dist/check.js` 验证
  TypeScript 后端逐字节重现每个 fixture 的 `expected_sha256`。任何
  分歧都让 job 非零退出 —— SHA 相等是必要条件，绝不模糊匹配。
* `conformance-go` job：在 `impl/go/` 下构建 Go 后端，跑
  `go run ./cmd/check`。它载入同一个 `manifest.json`，验证每个 fixture
  在 Go 移植上也复现同样的 SHA-256。Go 1.22，纯标准库，无任何第三方
  依赖。

Lean job 在缓存命中时约 5 分钟，冷缓存约 25 分钟。参考实现全部约 30 秒
跑完。一致性 job 不到 1 分钟。

---

## 许可

数学形式文档（`chanlun.md`、`chanlun.zh.md`）、Lean 形式化、参考实现和
CI 工作流按 MIT 许可发布（见 [`LICENSE`](LICENSE)，如果仓库中存在）。
缠论本身属于缠中说禅的传承。
