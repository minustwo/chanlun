// Shared Chanlun pipeline types.
//
// Faithful port of conformance/chanlun-v1/reference_backend/*.py - all integer-core.
// The shape of every record matches the reference dicts EXACTLY by key set;
// canonicalisation re-sorts keys, so insertion order in TypeScript objects does
// not matter, only the key/value set itself.

export interface Bar {
  l: number;
  h: number;
}

export type FractalKind = "top" | "bottom";

export interface Fractal {
  idx: number;
  kind: FractalKind;
  h: number;
  l: number;
}

export type StrokeDir = "up" | "down";

export interface Stroke {
  from_idx: number;
  to_idx: number;
  dir: StrokeDir;
  from_p: number;
  to_p: number;
}

export type StrokeDisposition = "first" | "absorbed" | "emit" | "residue";

export interface StrokeElement {
  idx: number;
  lo: number;
  hi: number;
}

export type ZhongshuZone = "first3" | "all";

export interface ZhongshuCenter {
  start: number;
  end: number;
  ZD: number;
  ZG: number;
  n: number;
}

export type TrendType =
  | "consolidation"
  | "trend_up"
  | "trend_down"
  | "mixed"
  | "none";
