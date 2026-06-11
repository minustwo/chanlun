// 笔 (Stroke, Def-4 + Lemma 2) - leftmost-greedy alternating anchor walk.
// Faithful port of conformance/chanlun-v1/reference_backend/strokes.py
//
// Fix dmin in N_{>0}. Walk the 分型 (fractal) sequence with a single alternating
// ANCHOR (leftmost-greedy):
//   - same-kind fractal -> keep the extremal representative (pick_rep).
//   - opposite-kind + (idx gap) >= dmin -> EMIT a stroke (anchor->f) and re-anchor.
//   - opposite-kind but too close (gap < dmin) -> DROP it (named 笔 residue).
//
// dispositions[i] is the per-fractal classification (exhaustion witness).

import type {
  Fractal,
  Stroke,
  StrokeDisposition,
} from "./types.js";

function pickRep(cur: Fractal, cand: Fractal): Fractal {
  if (cur.kind === "top") {
    return cand.h > cur.h ? cand : cur;
  }
  // bottom
  return cand.l < cur.l ? cand : cur;
}

export interface StrokesResult {
  strokes: Stroke[];
  dispositions: StrokeDisposition[];
}

export function strokes(fractals: Fractal[], dmin: number): StrokesResult {
  let anchor: Fractal | null = null;
  const out: Stroke[] = [];
  const disp: StrokeDisposition[] = [];
  for (const f of fractals) {
    if (anchor === null) {
      anchor = f;
      disp.push("first");
      continue;
    }
    if (f.kind === anchor.kind) {
      anchor = pickRep(anchor, f);
      disp.push("absorbed");
    } else if (f.idx - anchor.idx >= dmin) {
      // opposite & far -> emit + re-anchor
      const aPrice = anchor.kind === "top" ? anchor.h : anchor.l;
      const fPrice = f.kind === "top" ? f.h : f.l;
      out.push({
        from_idx: anchor.idx,
        to_idx: f.idx,
        dir: f.kind === "top" ? "up" : "down",
        from_p: aPrice,
        to_p: fPrice,
      });
      anchor = f;
      disp.push("emit");
    } else {
      // opposite but too close -> named residue
      disp.push("residue");
    }
  }
  return { strokes: out, dispositions: disp };
}
