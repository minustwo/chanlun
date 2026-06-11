# Chanlun-v1 — Go 一致性后端

`conformance/chanlun-v1/reference_backend/*.py` 的忠实纯标准库 Go 移植；在
§15 SHA 等同律下，逐字节通过 FROZEN `chanlun-v1` 语料库的全部 48 个 fixture。

## 这是什么

语料库 `conformance/chanlun-v1` 是缠论 pipeline 的 FROZEN 多语言一致性规范
（48 fixture × 6 stage，按字节锁定的 SHA-256；
`corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`）。
任一语言的 Phase-3 实现，当且仅当它在每个 fixture 的 `input` 上的分解结果在
规范化后产生的 SHA-256 等于该 fixture 的 `expected_sha256` 时，才算一致。

本模块即 Go 语言的 Phase-3 实现。其特征：

* **忠实移植**，不是重新推导。`internal/chanlun/*.go` 的每个文件都逐行
  对应 `reference_backend/*.py`；唯一可能出现偏差的地方就是规范 JSON 的
  字节编码层（核心要点，详见下文）。
* **纯标准库**，零第三方依赖（`go.mod` 不列任何依赖）。
* **整数语义**，与 Python 参考一致。若输入 fixture 出现浮点数，则被显式
  命名为结构性 residue，解码器直接拒绝。
* **严格六个 stage**，与语料库一致：`normalize`、`fractal`、`stroke`、
  `zhongshu`、`trend_type`、`pipeline`。超出语料库的 stage（segment、
  level-recursion、walk-decomposition）属于 Lean 库而非一致性语料库，故
  此处不予移植。

## 运行

在仓库根目录下：

```bash
cd impl/go
go build ./...
go run ./cmd/check
```

预期输出：

```
chanlun-v1 Go conformance check: 48 fixtures
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.
```

需要 Go 1.22 或更新。除此以外无其它构建前置条件。

## 目录结构

```
impl/go/
  go.mod                                    # module github.com/minustwo/chanlun/impl/go (Go 1.22)
  cmd/check/main.go                         # 一致性 harness（载入 manifest -> 跑各 stage -> 比对 SHA-256）
  internal/chanlun/
    canon.go                                # 规范 JSON 编码器 + SHA-256
    decode.go                               # JSON -> 类型化 Value 树（保留 int 语义）
    normalize.go                            # 算法 N（包含处理，附录 A）
    fractal.go                              # 定义 3 顶/底分型分类
    strokes.go                              # 定义 4 + 引理 2 笔的贪心
    zhongshu.go                             # 中枢（>=3 重叠）分解（带 zone 闸门）
    trend_type.go                           # 盘整 / trend_up / trend_down / mixed / none
    pipeline.go                             # 端到端 run_full
    stage.go                                # stage 派发（对照 example_phase3_check.py）
  README.md                                 # 英文版
  README.zh.md                              # 本文件
```

## Stage 对照（Go ↔ Python）

| Stage      | Go 文件                          | Python 文件                          |
|------------|----------------------------------|--------------------------------------|
| normalize  | `internal/chanlun/normalize.go`  | `reference_backend/normalize.py`     |
| fractal    | `internal/chanlun/fractal.go`    | `reference_backend/fractal.py`       |
| stroke     | `internal/chanlun/strokes.go`    | `reference_backend/strokes.py`       |
| zhongshu   | `internal/chanlun/zhongshu.go`   | `reference_backend/zhongshu.py`      |
| trend_type | `internal/chanlun/trend_type.go` | `reference_backend/trend_type.py`    |
| pipeline   | `internal/chanlun/pipeline.go`   | `reference_backend/pipeline.py`      |

## 规范 JSON 的选择（核心要点）

§15 SHA 等同律所比对的字节，是 Python 用下面这种规范方式产生的：

```python
json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
```

Go 标准库的 `encoding/json` 默认并不产生同样的字节：键名是 map 插入序
（或未指定顺序）输出的，也没有 `ensure_ascii=True` 的等价开关。因此我们
基于一个类型化的 `Value` 树自实现了一个小型规范编码器
（`internal/chanlun/canon.go`），具备以下行为：

1. **键名排序**——对象键按原始字符串键的 Unicode 码点序排序。chanlun-v1
   语料库中所有键都是 ASCII，所以等价于字典序的字节序，正是 Python 在
   `str` 键上 `sort_keys=True` 的行为。
2. **零空白**——`,` 与 `:` 两侧均无空格（对应 `separators=(",", ":")`）。
3. **`ensure_ascii=True`**——每一个码点 >= 0x7f 都转义成 `\uXXXX`。超出
   BMP 的码点使用 UTF-16 代理对（与 Python `json.dumps` 的实际行为完全
   一致）。标准短转义（`\"`、`\\`、`\b`、`\f`、`\n`、`\r`、`\t`）照常
   使用；其它控制字符（< 0x20）使用 `\u00XX` 输出。
4. **整数仍为整数**——JSON 解码使用 `json.Decoder.UseNumber()`，并拒绝
   任何包含 `.`、`e`、`E` 的 token。语料库为整数语义；若把出现的浮点数
   悄然降为 `int64`（或反过来把 `int` 升为 `float64` 并输出 `123.0`），
   会静默打破 SHA 等同。

结果：在 chanlun-v1 语料库上，每一个 stage 的输出字节都与 Python 参考的
规范字节完全一致——全部 48 个 `expected_sha256` 重新计算都对，而 harness
对 `corpus_sha256` 的整体重算也复现了 manifest 中的
`df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`。

如果将来的 fixture 引入 ASCII-键整数语义之外的值（例如含多字节码点的
UTF-8 键，或非整数），规范编码器仍会对字符串输出 Python 一致的字节
（通过 `\uXXXX` 带代理处理的显式路径），但非整数会触发命名 residue ——
今天的语料库契约不允许这种情况。

## 源流

§15 SHA 等同律与 FROZEN 语料库的纪律源自上游证明工程
（`minustwo/codex-proof-workbench`）。`conformance/chanlun-v1/reference_backend/`
的 Python 参考是 stage 语义的唯一权威；本 Go 移植精确复现这套语义。
本目录不发明任何后端逻辑——与 Python 的偏差仅限于规范 JSON 输出层；SHA
等同闸门即是检测漂移的回归测试。

## CI

每次 push / PR 上跑这个 harness 的 CI 任务名为 `conformance-go`，写在
`.github/workflows/chanlun-gate.yml`。它用 `actions/setup-go@v5` 安装
Go 1.22，然后跑：

```bash
cd impl/go
go build ./...
go run ./cmd/check
```

非零退出码即 fail。SHA 等同是法律：一个字节不对就是 FAIL，绝不静默跳过。
