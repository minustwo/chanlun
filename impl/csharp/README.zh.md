# chanlun-v1 C# / .NET 后端

chanlun-v1 流水线的 C# / .NET 8 整数核移植。带本地 conformance harness，对全部
48 条 fixtures 与 FROZEN 的 `conformance/chanlun-v1` corpus 做 byte-for-byte
SHA-256 等值比对。

SHA-equality 就是律法。差一个字节就 FAIL。没有模糊比较，没有 "约等于"，没有
float 容差 —— chanlun-v1 corpus 全程整数核。

## 源流

C# 移植对照
`conformance/chanlun-v1/reference_backend/` 的纯 Python 参考实现 +
`impl/go/internal/chanlun/` 的 Go 移植。Python 参考是 GROUND TRUTH；
`impl/ts`、`impl/go`、`impl/csharp` 间一旦分歧，以 Python 为准。

## 目录

```
impl/csharp/
  Chanlun.sln                            # solution
  src/
    Chanlun/                             # 库
      Chanlun.csproj                     # net8.0 库
      Types.cs                           # Bar, Fractal, Stroke, Element, Center, PipelineResult
      Canonical.cs                       # canonical JSON 编码器 + SHA-256 + 解码器
      Normalize.cs                       # Algorithm N (包含处理)
      Fractal.cs                         # Def-3 分型分类器
      Strokes.cs                         # Def-4 + Lemma 2 笔贪心
      Zhongshu.cs                        # 走势中枢分解 (zone gate: first3 / all)
      TrendType.cs                       # 走势类型分类器 (盘整/上涨/下跌/混合/无)
      Pipeline.cs                        # 端到端流水线 + 单 stage 分发
    Chanlun.Check/                       # conformance harness
      Chanlun.Check.csproj               # net8.0 exe
      Program.cs                         # 入口：加载 manifest、跑每个 stage、SHA-256 比对
```

## 构建

```
cd impl/csharp
dotnet restore
dotnet build -c Release --no-restore
```

## 本地跑 conformance harness

```
cd impl/csharp
dotnet run -c Release --no-build --project src/Chanlun.Check/Chanlun.Check.csproj
```

Harness 会从当前工作目录向上查找
`conformance/chanlun-v1/manifest.json`，所以从仓库根目录也能跑。

期望输出：

```
chanlun-v1 C# conformance check: 48 fixtures
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.
```

全过 exit 0，任一字节级偏差 exit 1。

## Canonical JSON (字节锁定的部分)

SHA-256 的输入是 canonical JSON 字节，必须 byte-for-byte 等于 Python 的
`json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)`。
`System.Text.Json` 默认不排序 key（保留插入序），escape 策略也跟 Python 不同，
所以我们在 typed `Value` 树上手写了 emitter（Canonical.cs）。

要点：

* Object key 用 `StringComparer.Ordinal` 排序（= Python str 排序在 ASCII 范围
  = 字典序 UTF-8 字节序）。chanlun-v1 corpus 的 key 全 ASCII。
* 分隔符 `,` 和 `:`，无任何空白。
* 字符串短转义 `\\`, `\"`, `\b`, `\f`, `\n`, `\r`, `\t`；控制字符和非 ASCII
  字符走 `\uXXXX`（BMP 外用代理对），完全对齐 Python `ensure_ascii=True`。
* 数字以 `long` 整数发出，使用 `InvariantCulture`，避免 locale 把千分位或
  小数点带进来。
* corpus 是整数核：解码器拒绝任何非整数数字，绝不静默降级。

## 一致性状态

* 全部 48 条 fixtures byte-identical SHA-256 通过 FROZEN chanlun-v1 spec
  （本地 + CI 的 `conformance-csharp` job 都验证）。
* 无运行时依赖（System.Text.Json 是 BCL 自带）。

## 为什么用 .NET 8

LTS、稳定，且是 `actions/setup-dotnet@v4` 配 `dotnet-version: '8.0.x'`
能拉到的版本，跟 chanlun-gate.yml 的 conformance-csharp job 对齐。
