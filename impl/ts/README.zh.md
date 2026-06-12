# impl/ts —— chanlun-v1 的 TypeScript 后端

冻结的 `chanlun-v1` 语料库的忠实、纯标准库 TypeScript 移植，逐字节
等价于 Python 参考实现。

English version: [README.md](README.md).

## 这是什么

`impl/ts/` 是 `conformance/chanlun-v1/reference_backend/` 中 Python
参考实现的 TypeScript 移植。已被 Lean 内核证明的六个阶段在 TypeScript
中实现，零运行时依赖：

| 阶段         | TypeScript 模块                | Python 源                                                     | Lean 定理                  |
| ------------ | ------------------------------ | ------------------------------------------------------------ | -------------------------- |
| `normalize`  | `src/normalize.ts`             | `reference_backend/normalize.py`                             | `Chanlun.Normalize`        |
| `fractal`    | `src/fractal.ts`               | `reference_backend/fractal.py`                               | `Chanlun.Fractal`          |
| `stroke`     | `src/strokes.ts`               | `reference_backend/strokes.py`                               | `Chanlun.Stroke`           |
| `zhongshu`   | `src/zhongshu.ts`              | `reference_backend/zhongshu.py`                              | `Chanlun.Zhongshu`         |
| `trend_type` | `src/trend_type.ts`            | `reference_backend/trend_type.py`                            | `Chanlun.TrendType`        |
| `pipeline`   | `src/pipeline.ts`              | `reference_backend/pipeline.py`                              | 组合流水线契约             |

`chanlun-v1` 之外的六个阶段（走势分解、三类买卖点、背驰、中枢延伸、
级别递归、线段）尚未在此移植 —— 它们会随未来的 `chanlun-v2` /
`chanlun-v3` 语料库一起到来。

## 来源谱系

本后端继续延伸的信任链：

```
chanlun.zh.md（定义 2-5、17/20/24 课）
  -> lean/Chanlun/*.lean（内核验证、无 sorry 的定理）
  -> conformance/chanlun-v1/reference_backend/*.py（独立 Python 参考实现）
  -> impl/ts/src/*.ts  ==SHA==>  conformance/chanlun-v1/fixtures/*.json
```

每一环都被检查：Lean 内核检查证明；Python 参考实现由 `grounding/` 在
数十万随机序列上加突变测试共同压力测试；语料库由 `corpus_sha256` 字节
冻结；本 TS 后端必须逐字节重现每个 fixture 的 `expected_sha256`。

## SHA 相等规则

> 每个阶段输出的规范 JSON 的 SHA-256 必须等于对应 fixture 的
> `expected_sha256`。**差一个字节 ⇒ FAIL**，非零退出。不模糊匹配，
> 不浮点容差，不「约等于」。

真正无法重现的 fixture 必须记录为开放问题，在后续工作中解决，绝不
静默跳过。CI gate 是唯一的裁判。

## 本地运行

```bash
cd impl/ts
npm ci --omit=optional   # 仅安装 typescript + @types/node devDeps
npx tsc                  # 编译到 dist/
node dist/check.js       # 运行 48-fixture 验证；全部通过才退出 0
```

预期输出：

```
chanlun-v1 phase-3 check, backend = impl/ts
  corpus_sha256 = df9c4f7ef0ca42bde51ed4db9ee0e4b13c8a11776e14324cfb6b9d32af7dd5c5

Result: 48 PASS, 0 FAIL
```

`npm run check` 是 `tsc && node dist/check.js` 的快捷方式。

## CI

`.github/workflows/chanlun-gate.yml` 中的 `conformance-ts` job 在
Hosted Ubuntu 上（Node 20）跑同一循环。CI 绿是合规的唯一证明。

## 设计说明

- **零运行时依赖。** `package.json` 仅声明 `typescript` 和 `@types/node`
  作为 devDeps。运行时使用 Node 自带的 `node:crypto`（计算 SHA-256）
  和 `node:fs/promises`（读取 fixture）。除此之外无其他。
- **整数核心。** 语料库只包含整数 K 线、分型、价格、中枢区间。
  `canonical.ts` 拒绝非整数数字 —— 这是**有意**的，防止任何浮点
  飘移悄悄偏离 Python 参考实现。
- **规范 JSON。** `src/canonical.ts` 严格镜像 Python 的
  `json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True)`：
  键按字典序排序、无空白、非 ASCII 转义为 `\uXXXX`。语料库的
  `corpus_sha256` 就是在这种编码下计算的，复现它必须**逐字节**匹配
  这种编码。
- **纯函数、无共享状态。** 每个阶段都是普通 JSON 对象上的无状态
  函数，匹配参考实现的纯数据协议。

## 文件

```
impl/ts/
  package.json          - 仅 devDeps（typescript、@types/node）
  tsconfig.json         - ES2022 / strict / 无 source map
  check.ts              - 48-fixture 验证脚本（入口）
  src/
    types.ts            - 共享接口类型（Bar、Fractal、Stroke、…）
    normalize.ts        - 算法 N（附录 A 包含处理）
    fractal.ts          - Def-3 顶/底分型分类器
    strokes.ts          - Def-4 + 引理 2 最左贪心 笔 walk
    zhongshu.ts         - >=3 重叠 中枢 分解（first3 / all）
    trend_type.ts       - 17 课 盘整 / 趋势 分类器
    pipeline.ts         - 从 bars 到 trend_type 的端到端流水线
    canonical.ts        - Python 兼容的规范 JSON 编码器
```
