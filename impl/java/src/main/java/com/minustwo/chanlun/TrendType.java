// TrendType.java — 走势类型 classifier, faithful port of
// conformance/chanlun-v1/reference_backend/trend_type.py:classify.
//
//   0 centers           -> "none"
//   1 center            -> "consolidation"
//   >=2, all step up    -> "trend_up"
//   >=2, all step down  -> "trend_down"
//   otherwise           -> "mixed"  (named residue, never silent)
//
// Step direction prev->cur is +1 if cur.ZD > prev.ZG, -1 if cur.ZG < prev.ZD,
// 0 otherwise (overlap / no clean step).
package com.minustwo.chanlun;

import java.util.List;

import com.minustwo.chanlun.Types.Center;

public final class TrendType {

    private TrendType() {}

    private static int stepDir(Center prev, Center cur) {
        if (cur.ZD() > prev.ZG()) return +1;
        if (cur.ZG() < prev.ZD()) return -1;
        return 0;
    }

    public static String classify(List<Center> centers) {
        int n = centers.size();
        if (n == 0) return Types.TREND_NONE;
        if (n == 1) return Types.TREND_CONSOLIDATION;
        boolean allUp = true, allDown = true;
        for (int k = 0; k < n - 1; k++) {
            int d = stepDir(centers.get(k), centers.get(k + 1));
            if (d != +1) allUp = false;
            if (d != -1) allDown = false;
        }
        if (allUp) return Types.TREND_UP;
        if (allDown) return Types.TREND_DOWN;
        return Types.TREND_MIXED;
    }
}
