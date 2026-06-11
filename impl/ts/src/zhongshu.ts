// 中枢 (Zhongshu / center) decomposition - lesson 17/20.
// Faithful port of conformance/chanlun-v1/reference_backend/zhongshu.py
//
// Scan for >=3 consecutive elements with a COMMON overlap:
//   ZD = max(lows of the first 3); ZG = min(highs of the first 3).
// A 中枢 forms iff ZD <= ZG (genuine overlap). Subsequent elements that still
// overlap the live test zone join it. The first element that does NOT overlap
// terminates the 中枢; the next 中枢 starts after.
//
// zone ('first3' | 'all'): under 'first3' the test zone stays the initial
// [ZD, ZG]; under 'all' the live test zone is re-tightened to the running
// overlap of all members as they join (a stricter reading).
//
// The PUBLISHED [ZD, ZG] is ALWAYS the first-3 core (the standard 缠论 中枢区间).

import type { StrokeElement, ZhongshuCenter, ZhongshuZone } from "./types.js";

export function zhongshu(
  els: StrokeElement[],
  zone: ZhongshuZone = "first3"
): ZhongshuCenter[] {
  const centers: ZhongshuCenter[] = [];
  const n = els.length;
  let i = 0;
  while (i + 2 < n) {
    const ZD = Math.max(els[i].lo, els[i + 1].lo, els[i + 2].lo);
    const ZG = Math.min(els[i].hi, els[i + 1].hi, els[i + 2].hi);
    if (ZD <= ZG) {
      const members: number[] = [i, i + 1, i + 2];
      let zd = ZD;
      let zg = ZG;
      let j = i + 3;
      while (j < n && els[j].lo <= zg && els[j].hi >= zd) {
        members.push(j);
        if (zone === "all") {
          zd = Math.max(zd, els[j].lo);
          zg = Math.min(zg, els[j].hi);
        }
        j++;
      }
      centers.push({
        start: i,
        end: members[members.length - 1],
        ZD,
        ZG,
        n: members.length,
      });
      i = members[members.length - 1] + 1;
    } else {
      i += 1;
    }
  }
  return centers;
}
