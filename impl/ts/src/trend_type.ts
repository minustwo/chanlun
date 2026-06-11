// 走势类型 (TrendType / lesson 17) - classify a completed 走势 by 中枢 count + direction.
// Faithful port of conformance/chanlun-v1/reference_backend/trend_type.py
//
//   0 中枢                                 -> none
//   1 中枢                                 -> consolidation
//   >= 2 中枢, all steps up   (依次同向)   -> trend_up
//   >= 2 中枢, all steps down (依次同向)   -> trend_down
//   >= 2 中枢, NOT all-same-direction      -> mixed (named residue)
//
// A "step" between consecutive centers is +1 if next.ZD > prev.ZG (strictly above),
// -1 if next.ZG < prev.ZD (strictly below), 0 otherwise.

import type { TrendType, ZhongshuCenter } from "./types.js";

function stepDir(prev: ZhongshuCenter, cur: ZhongshuCenter): number {
  if (cur.ZD > prev.ZG) return +1;
  if (cur.ZG < prev.ZD) return -1;
  return 0;
}

export function classify(centers: ZhongshuCenter[]): TrendType {
  const n = centers.length;
  if (n === 0) return "none";
  if (n === 1) return "consolidation";
  const dirs: number[] = [];
  for (let k = 0; k < n - 1; k++) {
    dirs.push(stepDir(centers[k], centers[k + 1]));
  }
  if (dirs.every((d) => d === +1)) return "trend_up";
  if (dirs.every((d) => d === -1)) return "trend_down";
  return "mixed";
}
