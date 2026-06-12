// 走势类型 classifier — faithful port of
// conformance/chanlun-v1/reference_backend/trend_type.py:classify.
//
//   0 centers           -> "none"
//   1 center            -> "consolidation"
//   >=2 all stepping up -> "trend_up"
//   >=2 all stepping dn -> "trend_down"
//   otherwise           -> "mixed"  (named residue, never silent)
//
// step_dir(prev,cur) = +1 if cur.ZD > prev.ZG, -1 if cur.ZG < prev.ZD, 0 else.

namespace Chanlun;

public static class TrendTypeOps
{
    public static string Classify(IReadOnlyList<Center> centers)
    {
        int n = centers.Count;
        if (n == 0) return TrendTypes.None;
        if (n == 1) return TrendTypes.Consolidation;
        bool allUp = true, allDown = true;
        for (int k = 0; k < n - 1; k++)
        {
            int d = StepDir(centers[k], centers[k + 1]);
            if (d != +1) allUp = false;
            if (d != -1) allDown = false;
        }
        if (allUp) return TrendTypes.Up;
        if (allDown) return TrendTypes.Down;
        return TrendTypes.Mixed;
    }

    private static int StepDir(Center prev, Center cur)
    {
        if (cur.ZD > prev.ZG) return +1;
        if (cur.ZG < prev.ZD) return -1;
        return 0;
    }
}
