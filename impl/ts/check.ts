// Phase-3 conformance harness for the TypeScript backend.
//
// Mirrors conformance/chanlun-v1/example_phase3_check.py: for every fixture in
// the FROZEN chanlun-v1 manifest, run the TS pipeline on `input`, canonicalize
// to JSON with the SAME rules Python uses (sort_keys, separators=(',', ':'),
// ensure_ascii), SHA-256 the bytes, compare against expected_sha256.
//
// All 48 fixtures must pass byte-for-byte. A single divergence => non-zero exit.
// No fuzzy match, no float tolerance - SHA-equality is the law (§15).

import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { canonical } from "./src/canonical.js";
import { normalizeN } from "./src/normalize.js";
import { extractFractals } from "./src/fractal.js";
import { strokes as strokesStage } from "./src/strokes.js";
import { zhongshu as zhongshuStage } from "./src/zhongshu.js";
import { classify as classifyStage } from "./src/trend_type.js";
import { DMIN, runFull } from "./src/pipeline.js";

interface ManifestEntry {
  id: string;
  stage: string;
  file: string;
  input_sha256: string;
  expected_sha256: string;
  fixture_sha256: string;
}

interface Manifest {
  version: string;
  corpus_sha256: string;
  count: number;
  entries: ManifestEntry[];
}

function backend(stage: string, input: unknown): unknown {
  switch (stage) {
    case "normalize":
      return normalizeN(input as Parameters<typeof normalizeN>[0]);
    case "fractal":
      return extractFractals(input as Parameters<typeof extractFractals>[0]);
    case "stroke": {
      const i = input as { fractals: Parameters<typeof strokesStage>[0]; dmin: number };
      const { strokes, dispositions } = strokesStage(i.fractals, i.dmin);
      return { strokes, dispositions };
    }
    case "zhongshu": {
      const i = input as {
        elements: Parameters<typeof zhongshuStage>[0];
        zone: Parameters<typeof zhongshuStage>[1];
      };
      return zhongshuStage(i.elements, i.zone);
    }
    case "trend_type":
      return classifyStage(input as Parameters<typeof classifyStage>[0]);
    case "pipeline": {
      const i = input as {
        bars: Parameters<typeof runFull>[0];
        dmin?: number;
        zone?: Parameters<typeof runFull>[2];
      };
      return runFull(i.bars, i.dmin ?? DMIN, i.zone ?? "first3");
    }
    default:
      throw new Error(`unknown stage: ${stage}`);
  }
}

function sha256Hex(bytes: Uint8Array): string {
  const h = createHash("sha256");
  h.update(bytes);
  return h.digest("hex");
}

async function main(): Promise<number> {
  // Resolve conformance/chanlun-v1/ relative to the compiled check.js location,
  // walking up from impl/ts/dist/ to the repo root.
  const here = dirname(fileURLToPath(import.meta.url));
  // dist/check.js -> dist -> ts -> impl -> repo root
  const repoRoot = resolve(here, "..", "..", "..");
  const corpusDir = resolve(repoRoot, "conformance", "chanlun-v1");

  const manifestText = await readFile(resolve(corpusDir, "manifest.json"), "utf-8");
  const manifest = JSON.parse(manifestText) as Manifest;

  console.log("chanlun-v1 phase-3 check, backend = impl/ts");
  console.log(`  corpus_sha256 = ${manifest.corpus_sha256}`);

  let fails = 0;
  for (const entry of manifest.entries) {
    const fixtureText = await readFile(resolve(corpusDir, entry.file), "utf-8");
    const fixture = JSON.parse(fixtureText) as {
      stage: string;
      input: unknown;
      expected_sha256: string;
    };
    let actual: unknown;
    try {
      actual = backend(fixture.stage, fixture.input);
    } catch (e) {
      const msg = e instanceof Error ? `${e.name}: ${e.message}` : String(e);
      console.log(`  [FAIL] ${entry.id.padEnd(60)} backend raised ${msg}`);
      fails += 1;
      continue;
    }
    const bytes = new TextEncoder().encode(canonical(actual));
    const actSha = sha256Hex(bytes);
    if (actSha !== entry.expected_sha256) {
      console.log(
        `  [FAIL] ${entry.id.padEnd(60)} actual sha=${actSha.slice(0, 12)}... expected sha=${entry.expected_sha256.slice(0, 12)}...`
      );
      fails += 1;
    }
  }

  const total = manifest.count;
  console.log();
  console.log(`Result: ${total - fails} PASS, ${fails} FAIL`);
  return fails ? 1 : 0;
}

main()
  .then((code) => process.exit(code))
  .catch((err) => {
    console.error(err);
    process.exit(2);
  });
