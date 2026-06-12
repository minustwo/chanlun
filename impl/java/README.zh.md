# Chanlun-v1 — Java 一致性后端

`conformance/chanlun-v1/reference_backend/*.py` 的忠实 Java 移植，按
SHA-equality 字节相等通过 `chanlun-v1` 冻结语料库的 48 个 fixture。

## 是什么

`conformance/chanlun-v1` 是缠论 pipeline 的多语言冻结一致性规范
（48 个 fixture × 6 个 stage，按 SHA-256 字节锁定；
`corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5`）。
任意语言的实现是 conformant 当且仅当对每个 fixture 的 `input`
做出的分解，规范化（canonical）字节后 SHA-256 与 `expected_sha256`
完全相等。

此模块是 Java 实现：

* **忠实移植**，不是重新设计。`src/main/java/com/minustwo/chanlun/*.java`
  每个文件逐行对应 Python `reference_backend/*.py` 与 Go
  `impl/go/internal/chanlun/*.go`，使得差异只可能出现在 canonical-JSON
  字节编码（见下）。
* **零运行时依赖** —— 纯 Java + 标准库。手写 JSON 解析器 +
  canonical 编码器，避免 Jackson / Gson 的插入顺序 / `ensure_ascii`
  细节配置陷阱。
* **整数核**：与 Python 参考相同，输入中的浮点会被解析器明确拒绝，
  绝不静默截断。
* **6 个 stage**：`normalize`、`fractal`、`stroke`、`zhongshu`、
  `trend_type`、`pipeline`，与语料库一致。

## 文件结构

```
impl/java/
  pom.xml                                          Maven 构建（Java 17）
  src/main/java/com/minustwo/chanlun/
    Types.java                                     Value 树 + 记录类型
    Canonical.java                                 JSON 解析 + canonical 编码 + SHA-256
    Normalize.java                                 算法 N（chanlun.pdf 附录 A）
    Fractals.java                                  Def-3（分型）分类器
    Strokes.java                                   Def-4 + 引理 2 笔贪心
    Zhongshu.java                                  走势中枢分解
    TrendType.java                                 走势类型分类器
    Pipeline.java                                  端到端 run_full + stage 调度
  src/main/java/com/minustwo/chanlun/check/
    Check.java                                     conformance harness（main）
```

## 构建

```bash
cd impl/java
mvn -B -DskipTests package
```

产物：`target/chanlun-check.jar`，自包含可执行 jar（零运行时依赖，
因此无需 shaded）。

## 运行

```bash
java -jar target/chanlun-check.jar
```

harness 从当前目录向上查找 `conformance/chanlun-v1/manifest.json`，
因此从 `impl/java/` 或仓库根目录都能运行。预期输出：

```
chanlun-v1 Java conformance check: 48 fixtures
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.
```

退出码 0 = 48 个 fixture 全部字节相等通过；非零 = 至少一个字节级
差异（harness 对任何字节级不一致都退出非零）。

## Canonical-JSON

Python 参考用：

```python
json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
```

Java canonical 编码器（`Canonical.canonical`）字节相等地复现：

* **键按字典序排序** —— code-point / UTF-16 顺序；语料库中键都是
  ASCII，与 Python 一致。
* **无空白** —— `(",", ":")` 分隔符。
* **纯 ASCII 输出** —— 所有 >= 0x7f 的码点用 `\uXXXX` 转义；
  BMP 外码点用 UTF-16 代理对。
* **整数核** —— 解析器拒绝任何含 `.`、`e`、`E` 的数字。输入数据里
  混进浮点是一个 honest error，不是静默截断。

正是这三条保证了 SHA-256 比较的意义：一个字节都不能差。

## 状态

* 48 / 48 fixture 通过，SHA-256 字节相等地匹配 Python 参考与现有
  `impl/ts` / `impl/go` 移植。
* 本地用 OpenJDK 21 + Maven 3.9 验证通过。
* CI：`.github/workflows/chanlun-gate.yml` 中的 `conformance-java` job，
  每个 PR 自动跑 `java -jar target/chanlun-check.jar`
  （Temurin 21，5 分钟 timeout —— 与 TS / Go 同档）。
