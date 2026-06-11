// Definition 3 - 分型 (Fractal) classifier on a normalized bar sequence.
// Faithful port of conformance/chanlun-v1/reference_backend/fractal.py
//
// Top fractal at i:     H_i > H_{i-1} and H_i > H_{i+1} and L_i > L_{i-1} and L_i > L_{i+1}
// Bottom fractal at i:  L_i < L_{i-1} and L_i < L_{i+1} and H_i < H_{i-1} and H_i < H_{i+1}
// (Lemma 1: every interior position is exactly one of top / bottom / neither.)
//
// Boundary bars (idx 0, idx n-1) are not classified - Def-3 needs a 3-bar window.

import type { Bar, Fractal } from "./types.js";

function isTop(a: Bar, b: Bar, c: Bar): boolean {
  return b.h > a.h && b.h > c.h && b.l > a.l && b.l > c.l;
}

function isBottom(a: Bar, b: Bar, c: Bar): boolean {
  return b.l < a.l && b.l < c.l && b.h < a.h && b.h < c.h;
}

export function extractFractals(bars: Bar[]): Fractal[] {
  const out: Fractal[] = [];
  const n = bars.length;
  for (let i = 1; i < n - 1; i++) {
    const a = bars[i - 1];
    const b = bars[i];
    const c = bars[i + 1];
    if (isTop(a, b, c)) {
      out.push({ idx: i, kind: "top", h: b.h, l: b.l });
    } else if (isBottom(a, b, c)) {
      out.push({ idx: i, kind: "bottom", h: b.h, l: b.l });
    }
    // else NEITHER - drop (gap in idx reflects it)
  }
  return out;
}
