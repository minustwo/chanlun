# 缠论一致性语料库 `chanlun-v1`

> 缠论（缠中说禅）确定性分解流水线的可移植、语言无关测试套件。任何语言的后端只要能逐字节
> 重现每个 fixture 的 SHA-256 期望输出，即视为符合 `chanlun-v1`。消费本语料库无需 Python。

本语料库**冻结**缠论分解规范：`原始 K 线 → 包含处理 → 分型 → 笔 → 中枢 → 走势类型`。每个
fixture 以 canonical-JSON SHA-256 锁定（input 字节 → expected 输出字节）。差一个字节即不符合。
没有模糊比较。

## 文件清单

| 文件 | 内容 |
|---|---|
| `manifest.json` | 规范指针 + 每个 fixture 的 SHA-256 期望 + `corpus_sha256`（即一致性版本号）。 |
| `fixtures/*.json` | 每个 fixture 一个 JSON：`{ id, stage, input, expected, input_sha256, expected_sha256, fixture_sha256 }`。 |
| `reference_backend/` | 纯 Python 标准库参考实现（`normalize`、`fractal`、`strokes`、`zhongshu`、`trend_type`、`pipeline`）。 |
| `runner.py` | 参考 runner（< 100 行纯标准库）：对每个 fixture 重跑参考实现并断言字节相等。 |
| `generate_corpus.py` | 确定性 fixture 生成器（重跑产生相同字节）。 |
| `example_phase3_check.py` | Phase-3 实现者的模板脚本：加载 fixtures、跑自己的流水线、比对 SHA-256。 |

## 运行方式

```bash
# 验证每个 fixture 与冻结规范字节相等（参考 Python 后端）。
python3 conformance/chanlun-v1/runner.py
# 48 PASS, 0 FAIL => 符合 chanlun-v1。

# 显示每个 fixture 的 SHA（详细模式）。
python3 conformance/chanlun-v1/runner.py --verbose

# 重新生成语料库（确定性 — 字节相同）。
python3 conformance/chanlun-v1/generate_corpus.py
# 相同的 corpus_sha256 = 冻结的一致性版本号。
```

## 语料库内容

缠论流水线 6 个阶段，共 48 个 fixtures（`manifest.json` 的 `stage_counts`）。

| 阶段 | 数量 | 测试内容 |
|---|---:|---|
| `normalize` | 10 | 算法 N（`chanlun.zh.md` 附录 A）— 单趟包含处理。 |
| `fractal` | 7 | 定义 3 分型在 3 条 K 线窗口上的分类（顶/底）。 |
| `stroke` | 6 | 定义 4 + 引理 2 笔贪心（交替 + 间隔 `>= dmin`）。 |
| `zhongshu` | 9 | 中枢分解（≥3 重叠规则，`first3` 与 `all` 两种 zone gate）。 |
| `trend_type` | 8 | 走势类型分类（盘整 / 上涨趋势 / 下跌趋势 / mixed / none）参考第 17 课。 |
| `pipeline` | 8 | 端到端（K 线 → 走势类型）确定性种子游走。 |

每个分类都包含：

- **手工 fixtures** — 小型、命名清晰的用例，每个测试一个特定的不变量
  （例如 `normalize.hand_single_containment`、`fractal.hand_top`、`zhongshu.hand_no_overlap`）。
- **合成 fixtures** — 不同长度的种子随机游走输入，扩大覆盖率
  （例如 `normalize.synth_walk_seed101_n10`、`pipeline.synth_walk_seed3004_n320`）。

## 协议形状（Phase-3 后端读写的格式）

每个 fixture 为 canonical JSON：

```json
{
  "id":               "stroke.hand_one_down",
  "stage":            "stroke",
  "description":      "...",
  "input":            { "fractals": [...], "dmin": 3 },
  "expected":         { "strokes": [...], "dispositions": ["first","emit","residue"] },
  "input_sha256":     "<canonical(input) 的 sha256>",
  "expected_sha256":  "<canonical(expected) 的 sha256>",
  "fixture_sha256":   "<canonical(input) + '|' + canonical(expected) 的 sha256>"
}
```

### Canonical JSON

每一次 SHA-256 计算都通过以下方式产生字节：

```python
json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
```

即：键排序、无空白、非 ASCII 字符转义。每个 Phase-3 实现都必须逐字节重现这些字节方可合规。

### 各阶段输入/输出形状

| 阶段 | 输入 | 输出 |
|---|---|---|
| `normalize` | `[ {l:int, h:int}, ... ]` | `[ {l:int, h:int}, ... ]`（无相邻包含） |
| `fractal` | `[ {l:int, h:int}, ... ]`（规范化 K 线） | `[ {idx:int, kind:"top"|"bottom", h:int, l:int}, ... ]` |
| `stroke` | `{ fractals: [...], dmin: int }` | `{ strokes: [...], dispositions: ["first"|"absorbed"|"emit"|"residue", ...] }` |
| `zhongshu` | `{ elements: [{idx, lo, hi}, ...], zone: "first3"|"all" }` | `[ {start:int, end:int, ZD:int, ZG:int, n:int}, ... ]` |
| `trend_type` | `[ {start, end, ZD, ZG, n}, ... ]`（中枢） | `"consolidation"|"trend_up"|"trend_down"|"mixed"|"none"` |
| `pipeline` | `{ bars, dmin?, zone? }` | `{ normalized_bars, fractals, stroke_dispositions, strokes, stroke_elements, zhongshu_zone, zhongshu_centers, trend_type }` |

## 如何编写合规的 Phase-3 后端

1. **阅读规范**：
   - `chanlun.zh.md`（中文）/ `chanlun.md`（英文）— 定义 2-5、第 17/20/24 课。
   - `lean/Chanlun/*.lean` — 机器验证的定理（`fractal_slot_equiv_def3`、
     `normalize_no_adjacent_containment`、`stroke_emit_alternates_and_separates`...）。
   - `grounding/chanlun_*_grounding.py` — 纯 Python oracle（已被内核验证的 Lean 库下游 sealing）。
2. **在你的目标语言里实现**各个阶段。
3. **跑语料库**：对 `manifest.json` 中每条 `entries[i]`，
   - 加载 `fixtures/<file>.json`；
   - 在 `input` 上运行你的流水线；
   - 规范化输出（`sort_keys=True, separators=",:"`，非 ASCII 转义）；
   - `SHA-256(canonical_output)` 必须等于 `expected_sha256`。差一个字节就不合规。
4. **全部 48 个 fixtures 通过** → 你的后端符合 `chanlun-v1`。

请把 `example_phase3_check.py` 当成模板（整脚本约 60 行纯标准库）。

## 来源谱系（期望值从哪儿来）

```
                  第 17/20/24 课                     (chanlun.zh.md / chanlun.md — 形式系统)
                         |
                         v
                  Lean MWEs                          (lean/Chanlun/*.lean — 内核验证定理)
                         |
                         v
                  Python groundings                  (grounding/chanlun_*_grounding.py — 纯标准库 oracle，sealing)
                         |
                         v
                  参考后端                            (conformance/chanlun-v1/reference_backend/ — 独立模块)
                         |
                         v
                  Fixtures + manifest                (本语料库)
```

每一步都可审计。任何符合本语料库的 Phase-3 实现，根据传递性，亦符合已验证的 Lean 库。

## 版本

本版本为 `chanlun-v1`，**已冻结**。`manifest.json#corpus_sha256` 即为版本号：
**`df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`**。

新版本（`chanlun-v2`、...）会放在自己的目录下（`conformance/chanlun-v2/`）。v1 永不改动。
任何修改参考后端使得 fixture 的期望 SHA 发生变化都属于不向后兼容的改动，必须落到新版本里。

## CI gate

`chanlun-gate` workflow（`.github/workflows/chanlun-gate.yml`）在 push 到 `main` 和每个 PR
都跑 `python3 conformance/chanlun-v1/runner.py`。非零退出码即构建失败。这是托管 Ubuntu 上的
强制执行，确保冻结的规范保持冻结。

## §15 红线

> SHA 相等是唯一法律。差一个字节 = FAIL。不存在「近似相等」、不存在浮点容忍、不存在模糊匹配。
> 如果你放松了一个 fixture 让它通过，那么你已经破坏了规范。

如果 Phase-3 实现者觉得某个 fixture 的期望输出看起来不对，**不要**放松它。开一个
`[chanlun_v1_fixture_F_questionable_OPEN]` 命名残差工单，在 runner 输出中显式标记，
并在后续 `chanlun-v2` 语料库版本里解决。

## 纯标准库 runner

runner 只使用 Python 标准库（无 numpy、无 pandas、无任何外部依赖）。这使得任何 Phase-3
语言都能轻松镜像：canonical-JSON + SHA-256 是通用栈。
