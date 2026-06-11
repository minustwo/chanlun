// Algorithm N - 包含处理 (inclusion-normalization) - faithful port of
// conformance/chanlun-v1/reference_backend/normalize.py
//
// Chanlun.pdf Appendix A, transcribed: left-to-right; append Xi; whenever the
// last two elements A, B are in a CONTAINMENT relation (A subset B or B subset A)
// replace them with the directional merge C:
//   up-rule:   C = [max(L_A, L_B), max(H_A, H_B)]
//   down-rule: C = [min(L_A, L_B), min(H_A, H_B)]
// direction = the trend (up iff the new non-contained bar's high exceeds the
// prior top's high). Deterministic. Integer-core, no floats.

import type { Bar } from "./types.js";

function contained(a: Bar, b: Bar): boolean {
  // A subset B or B subset A (<= so shared boundaries count, per Appendix A).
  const aInB = b.l <= a.l && a.h <= b.h;
  const bInA = a.l <= b.l && b.h <= a.h;
  return aInB || bInA;
}

function merge(a: Bar, b: Bar, up: boolean): Bar {
  if (up) {
    return { l: Math.max(a.l, b.l), h: Math.max(a.h, b.h) };
  }
  return { l: Math.min(a.l, b.l), h: Math.min(a.h, b.h) };
}

export function normalizeN(xs: Bar[]): Bar[] {
  const stack: Bar[] = [];
  let up = true; // dir initial = up (matches the program's dir=1)
  for (const raw of xs) {
    const it: Bar = { l: raw.l, h: raw.h };
    if (stack.length === 0) {
      stack.push(it);
      continue;
    }
    const top = stack[stack.length - 1];
    if (contained(top, it)) {
      stack[stack.length - 1] = merge(top, it, up);
    } else {
      stack.push(it);
      up = it.h > top.h; // trend direction for the NEXT merge
    }
  }
  return stack;
}
