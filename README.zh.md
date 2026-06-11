# 缠论 —— 理论 + Lean 形式化

**缠论**（缠中说禅老师所传授的技术分析方法）的形式化几何分解系统：

* **理论文档**：[`chanlun.zh.md`](chanlun.zh.md)（数学形式）。
* **Lean 4 形式化**（`lean/Chanlun/`）：以下 11 个承重定理，全部 `sorry`-free，
  由 Hosted Ubuntu CI 的 Lean 内核验证。
* **纯 Python 接地**（`grounding/`）：每个 Lean 定理都有独立参考实现作为
  对照，并配有 §15 反例突变体。

English version: see [README.md](README.md).

> **致谢声明**：缠论本身属于缠中说禅的传承。[`chanlun.zh.md`](chanlun.zh.md)
> 中的数学形式是本仓库对 Lean 库的叙述形式；`lean/Chanlun/` 下的 Lean
> 模块才是可信工件。本目录贡献的 Lean 形式化在
> [`codex-proof-workbench`](https://github.com/minustwo/codex-proof-workbench)
> 证明工程中完成，迁移至此公开发布。

---

## 状态 —— 已证 vs 命名残差

Lean 库 `Chanlun`（`lake build Chanlun`）sorry-free，覆盖了发表版四段流水线
加上两个后续结构层（中枢 / 走势类型）。共 11 个模块：

| 模块 | 定理（chanlun.zh.md 索引） |
|---|---|
| `Chanlun.Fractal` | Def-3 分型：`fractal_slot_equiv_def3`、`def3_trichotomy`（引理 1）、`def3_admissible_classifies`、`def3_residue_iff_neither` |
| `Chanlun.Normalize` | 算法 N（包含处理，附录 A）：`normalize_no_adjacent_containment`（单次扫描 = 完全合并） |
| `Chanlun.Pipeline` | N → Def-3 组合：`pipeline_inclusion_normalized`、`pipeline_fractal_classification_well_defined` |
| `Chanlun.Stroke` | Def-4 笔（最左贪心）：`stroke_emits_separated`（B）、`stroke_emits_alternate`（A）、`strokes_separated` |
| `Chanlun.StrokeUniqueness` | 引理 2 强形式：`strokes_unique`（任何 `IsValidBi` = 流式输出的规范结果） |
| `Chanlun.Segment` | Def 5–16 + 定理 1（线段 + 参数化唯一段分解）：`segments_partition`（P）、`segments_terminate`（T）、`segment_advance_strictly_increasing` |
| `Chanlun.Zhongshu` | 中枢（17/20 课）：`zhongshu_valid`、`zhongshu_disjoint`、`extendEnd_ge`，参数化于 `ZoneGate ∈ {first3, all_}` |
| `Chanlun.TrendType` | 盘整 / 趋势（17 课）：`classify_total`、`classify_trend_monotone`（依次同向是真正的单调） |
| `Chanlun.BiReachableDeterminism` | 可达域确定性：`fractals_alternate_on_containment_free`（包含处理后 ⇒ 分型严格交替 ⇒ 三种笔端点读法在可达输入上完全重合） |
| `Chanlun.LevelRecursion` | 走势必完美（24 课）：`centerSize_ge_3`、`lift_strict_drop`（每次非终端 lift 元素数严格下降 ≥2 ⇒ 级别递归在 ≤ n/2 步内终止） |
| `Chanlun.WalkDecomposition` | 走势最大分解（17 课）：`decompose_partition`、`decompose_monotonic`、`decompose_type_homogeneous` |

### 诚实范围 —— 命名 OPEN 后续（尚未证明）

这些是按 Klaus 的 `[..._OPEN]` 纪律明确标注的命名残差：

* `[chanlun_inclusion_precondition]` —— Def-3 上游假定的前置条件
  `isInclusionNormalized`；由 pipeline 组合
  （`Chanlun.Pipeline.pipeline_inclusion_normalized`）卸载，但类型桥接显式
  命名。
* `[chanlun_segment_terminates_sub_OPEN]` —— `find_term` 的特征序列 Φ +
  重叠 admissibility 内部细节没有在 `Chanlun.Segment` 中重新推导；递归是
  参数化于最左 ≥ a 的契约 `find_term_ge`。
* `[chanlun_zhongshu_zone_gate_OPEN]` —— `first3` 与 `all_` 在约 12% 的
  元素序列上结果不同；两者都被证 `valid` + `disjoint`，但 gate 相对性
  被命名。
* `[chanlun_bi_to_endpoint_first_admissible_OPEN]` ——
  `Chanlun.StrokeUniqueness` 把 TO 端点读作最左的反向 admissible 分型；
  按 "到端 run 的极值" 字面强读可能在多分型 run 上不同。
* `[chanlun_bi_close_drop_named_residue_OPEN]` —— 反向且过近的分型
  （gap < δmin）被 `step` 静默丢弃；唯一性证明将丢弃视为 no-op。
* `[chanlun_stroke_output_order_lift_OPEN]` —— `strokes_separated` 通过
  `List.mem_reverse` 提升到用户面向的反向顺序；反向顺序上的交替性是
  另一个一行 lemma，留作 OPEN。
* `[chanlun_level_recursion_lift_function_OPEN]` —— 实际的
  `lift : List Element → Option (List Element)` 函数不在范围内；仅证明
  了承重的严格下降测度（终止性的承重一半）。
* `[chanlun_level_recursion_envelope_soundness_OPEN]` —— 每个第 (n+1)
  层 envelope 包含其成员的范围。
* `[chanlun_level_recursion_determinism_preservation_OPEN]` —— 确定性
  沿塔上提保持。
* `[chanlun_walk_decomposition_spec_unique_OPEN]` —— 走势分解唯一性的
  规范形式（任何满足 spec 的函数 = `decompose`）。
* `[chanlun_walk_decomposition_intervalnesting_OPEN]` —— 区间套 / 多级别
  嵌套分解。

这些 **不是** 静默漏洞 —— 每一个都命名，让下一轮明确知道要 discharge 哪个
残差。

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

`lake build Chanlun` 通过 ⇒ 11 个模块在 Lean 内核下 sorry-free。

### 运行接地

```bash
cd grounding
for f in chanlun_*_grounding.py; do
  echo "===== $f ====="
  PYTHONPATH=. python3 "$f"
done
```

每个 grounding 几秒内跑完（60k–240k 随机序列），打印一行 OK 摘要加上 §15
falsifiability 检查。无外部 Python 依赖；纯标准库 + `random`。

---

## 目录结构

```
chanlun/
├─ chanlun.md                         # 数学形式（英文）
├─ chanlun.zh.md                      # 数学形式（中文）
├─ README.md                          # 英文版
├─ README.zh.md                       # 本文件（中文）
├─ lakefile.lean, lean-toolchain      # Lean 4 构建配置（Mathlib v4.14.0）
├─ lean/Chanlun/                      # 11 个 Lean MWE 模块
│  ├─ Fractal.lean, Normalize.lean, Pipeline.lean
│  ├─ Stroke.lean, StrokeUniqueness.lean, Segment.lean
│  ├─ Zhongshu.lean, TrendType.lean, BiReachableDeterminism.lean
│  ├─ LevelRecursion.lean, WalkDecomposition.lean
├─ grounding/                         # 纯 Python 参考实现
│  ├─ chanlun_inclusion_grounding.py
│  ├─ chanlun_singlepass_idempotent_grounding.py
│  ├─ chanlun_stroke_grounding.py
│  ├─ chanlun_trend_type_grounding.py
│  ├─ chanlun_zhongshu_grounding.py
│  ├─ chanlun_bi_endpoint_multivalued_grounding.py
│  └─ chanlun_bi_kline_rule_grounding.py
├─ conformance/chanlun-v1/             # 冻结的一致性语料库（Phase-3 规范）
│  ├─ manifest.json                    # corpus_sha256 = 版本号
│  ├─ fixtures/*.json                  # 48 个（输入、期望、sha）fixtures
│  ├─ reference_backend/               # 独立纯标准库参考实现
│  ├─ runner.py                        # ~100 行纯标准库验证脚本
│  ├─ generate_corpus.py               # 确定性 fixture 生成器
│  ├─ example_phase3_check.py          # Phase-3 实现者模板
│  ├─ README.md, README.zh.md          # 完整规范文档（英 / 中）
├─ impl/pinescript/                    # PineScript v5 后端（文档化移植）
│  ├─ chanlun_indicator.pine           # 指标本体（贴进 TradingView）
│  ├─ PINESCRIPT_PORT.md               # 分阶段映射 + 13 条 NAMED-OPEN 残差
│  └─ README.md, README.zh.md          # 中英文使用文档（仅文档化移植 —— 见下）
└─ .github/workflows/chanlun-gate.yml  # Hosted Ubuntu CI：lake build + groundings + conformance + pinescript-lint
```

### PineScript 后端 —— 仅文档化移植

`impl/pinescript/` 是同一算法的 PineScript v5 移植版本，会把 分型/笔/中枢 画在
TradingView 真实的 K 线上。**它没有做一致性验证**：PineScript v5 无法在 CI 中读 fixture
语料或做 SHA-256 比对。诚实纪律把每个缺口都命名为 `[chanlun_v1_pinescript_<stage>_OPEN]`
残差（共 13 条 —— 见 `impl/pinescript/PINESCRIPT_PORT.md`）。CI 跑一个**纪律检查**
（`conformance-pinescript-lint`），核对反模式不存在、命名残差都在文档里 —— 但它**不是**
SHA-equality 一致性 gate。

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
  每个 fixture 逐字节匹配冻结规范；接着重新生成语料库并确认字节完全相同
  （以捕获参考实现的任何漂移）。`chanlun-v1` 的 `corpus_sha256` 即为
  一致性版本号：任何语言的 Phase-3 多语言实现要合规，必须重现每个
  fixture 的期望 SHA-256。

Lean job 在缓存命中时约 5 分钟，冷缓存约 25 分钟。Grounding 全部约 30 秒
跑完。Conformance 不到 1 分钟。

---

## 交叉引用

* 这些 MWE 文件的来源证明工程：
  [`codex-proof-workbench`](https://github.com/minustwo/codex-proof-workbench)
* 缠中说禅老师发表的 108 课是中枢、走势类型，以及后续工作中用到的买卖点
  几何钩子的真理来源。
* Mathlib v4.14.0 是唯一的库依赖。

---

## 许可

数学形式文档（`chanlun.md`、`chanlun.zh.md`）、Lean 形式化、接地脚本和
CI 工作流按 MIT 许可发布（见 [`LICENSE`](LICENSE)，如果仓库中存在）。
