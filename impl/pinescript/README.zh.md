# 缠论 —— PineScript v5 后端（文档化移植）

一个 PineScript v5 指标，把缠论的拆分流水线（包含处理 → 分型 → 笔 →
中枢 → 走势类型）画在 TradingView 的真实 K 线上。Pine 源代码移植的是
`conformance/chanlun-v1/reference_backend/` 里 Python 参考实现所用的
同一算法，适配到 PineScript 的「逐 bar 流式」求值模型。

> **重要说明**：这是一份**文档化移植**，不是一致性验证过的后端。
> TradingView / PineScript 在运行时无法读 `chanlun-v1` 的 fixture 语料，
> 也无法在 CI 里做 SHA-256 比对。任何分歧、任何验证缺口，都被显式列出。
> 详见 `PINESCRIPT_PORT.md` 中完整的映射表和限制清单。

## 文件清单

| 文件 | 用途 |
|---|---|
| `chanlun_indicator.pine` | PineScript v5 指标本体，加载到 TradingView 即用。 |
| `PINESCRIPT_PORT.md` | 分阶段映射注解、确认延迟约定、13 条已知限制。**先读这一份。** |
| `README.md` | 英文版本。 |
| `README.zh.md` | 本文件（中文）。 |

## 使用方法

1. 打开 TradingView，选定任意标的/周期。
2. 打开图表底部的 `Pine Editor`，把 `chanlun_indicator.pine` 的内容贴
   进一个新脚本。
3. 点击 `Save`（保存）→ `Add to chart`（加入图表）。
4. 调整参数：
   - `δmin`（默认 4）：笔的分离阈值。Chart-bar 与 normalized-bar 间隔
     的单位差异见 `PINESCRIPT_PORT.md §"stroke — Definition 4 +
     Lemma 2"`。
   - `Zhongshu zone gate`（`first3` 或 `all`）：中枢区间的选择；两种
     读法都在此支持（根 README 说明这种多解性）。
   - `Use barstate.isconfirmed`（默认 `true`）：保持开启以避免
     repaint。
5. 图表上会显示：
   - 每个已提交的归一化 bar 的 H/L 处的蓝色小点。
   - 每个分型中间 bar 上的 `T`（红，顶分型）/ `B`（绿，底分型）标签。
   - 笔：青绿线（上笔）/ 品红线（下笔）。
   - 中枢：黄色半透明矩形（`[ZD, ZG]`）。
   - 右上角一个总览标签：当前走势类型 + 各阶段计数。

## 来源谱系

```
chanlun.md / chanlun.zh.md                                          （理论原文）
        |
        v
lean/Chanlun/*.lean                                                 （Lean 内核证明）
        |
        v
conformance/chanlun-v1/reference_backend/*.py                       （Python 参考实现，批处理）
        |
        v
impl/pinescript/chanlun_indicator.pine                              （Pine v5，逐 bar 流式）
```

## 为什么没有 CI 验证

PineScript v5 没有公开的无头运行器，无法在运行时读 fixture 文件，
也无法把内部结构序列化成 SHA-256 可比对的输出。仓库 CI 跑了一个
**纪律检查**（`conformance-pinescript-lint`）：核对常见反模式不存在、
所有已记录限制都在文档里出现 —— 但它**不是**真正的一致性 gate。

如果要做真正的 SHA-equality CI gate，需要一份 Python/Node 的离线
harness，镜像 Pine 的逐 bar 逻辑，对整个语料跑一遍。这份 harness 在
`PINESCRIPT_PORT.md` 中列为后续工作，不在本范围内。

## 范围与限制

13 条已知限制。完整列表见 `PINESCRIPT_PORT.md §"Known limitations"`。
要点：

- **算法本身**，每一阶段，都和参考实现一致。文档化移植在**逻辑层面是
  忠实的**。
- δmin 间隔以**图表-bar 单位**度量，不是参考实现的**归一化-bar 单位**。
  后续重构需要维护一个归一化-bar 计数器并对其检验。
- 「走势」边界在 Pine 内拿不到，所以 `trend_type` 用最近 2 个中枢的
  滚动近似。
- 流式形态下的滑动-3 中枢检测在边角情形上可能和批处理实现略有差异
  （尚未给出反例，但也未排除）。

每一条都被记录，下一轮就知道要消解哪条。

## 许可

与仓库根目录一致（MIT，除非 `LICENSE` 另有说明）。
