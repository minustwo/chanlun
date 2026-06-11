// End-to-end Chanlun pipeline assembled from the standalone stage oracles.
// Faithful port of conformance/chanlun-v1/reference_backend/pipeline.py
//
//   raw_bars
//     -> normalizeN              -> normalized_bars
//     -> extractFractals         -> fractals
//     -> strokes(dmin=DMIN)      -> strokes + dispositions
//     -> strokesToElements       -> stroke_elements
//     -> zhongshu(zone)          -> zhongshu_centers
//     -> classify                -> trend_type
//
// Integer-core, deterministic pure functions throughout. The corpus FREEZES the
// byte-shape of run_full's output.

import type {
  Bar,
  Fractal,
  Stroke,
  StrokeDisposition,
  StrokeElement,
  TrendType,
  ZhongshuCenter,
  ZhongshuZone,
} from "./types.js";
import { normalizeN } from "./normalize.js";
import { extractFractals } from "./fractal.js";
import { strokes as strokesStage } from "./strokes.js";
import { zhongshu as zhongshuStage } from "./zhongshu.js";
import { classify as classifyStage } from "./trend_type.js";

// Default stroke separation (xinbi dmin = 4, proven faithful in
// chanlun_bi_kline_rule_grounding.py).
export const DMIN = 4;

export function normalize(bars: Bar[]): Bar[] {
  return normalizeN(bars);
}

export function fractals(normalizedBars: Bar[]): Fractal[] {
  return extractFractals(normalizedBars);
}

export function strokes(
  fractalList: Fractal[],
  dmin: number = DMIN
): { strokes: Stroke[]; dispositions: StrokeDisposition[] } {
  return strokesStage(fractalList, dmin);
}

export function strokesToElements(strokeList: Stroke[]): StrokeElement[] {
  const out: StrokeElement[] = [];
  for (let i = 0; i < strokeList.length; i++) {
    const s = strokeList[i];
    const lo = Math.min(s.from_p, s.to_p);
    const hi = Math.max(s.from_p, s.to_p);
    out.push({ idx: i, lo, hi });
  }
  return out;
}

export function zhongshu(
  elements: StrokeElement[],
  zone: ZhongshuZone = "first3"
): ZhongshuCenter[] {
  return zhongshuStage(elements, zone);
}

export function classify(centers: ZhongshuCenter[]): TrendType {
  return classifyStage(centers);
}

export interface FullPipelineResult {
  normalized_bars: Bar[];
  fractals: Fractal[];
  stroke_dispositions: StrokeDisposition[];
  strokes: Stroke[];
  stroke_elements: StrokeElement[];
  zhongshu_zone: ZhongshuZone;
  zhongshu_centers: ZhongshuCenter[];
  trend_type: TrendType;
}

export function runFull(
  bars: Bar[],
  dmin: number = DMIN,
  zone: ZhongshuZone = "first3"
): FullPipelineResult {
  const nb = normalize(bars);
  const fr = fractals(nb);
  const { strokes: st, dispositions: disp } = strokes(fr, dmin);
  const elems = strokesToElements(st);
  const centers = zhongshu(elems, zone);
  const trend = classify(centers);
  return {
    normalized_bars: nb,
    fractals: fr,
    stroke_dispositions: disp,
    strokes: st,
    stroke_elements: elems,
    zhongshu_zone: zone,
    zhongshu_centers: centers,
    trend_type: trend,
  };
}
