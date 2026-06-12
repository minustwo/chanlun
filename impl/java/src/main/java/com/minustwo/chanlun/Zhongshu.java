// Zhongshu.java — 走势中枢 decomposition, faithful port of
// conformance/chanlun-v1/reference_backend/zhongshu.py:zhongshu.
//
// Scan elements (each {idx, lo, hi}); a center forms iff
// max(lo of first 3) <= min(hi of first 3) (ZD <= ZG). Extend with elements
// still overlapping [zd, zg]. Zone gate:
//   "first3" - the test zone stays at the first-3 overlap;
//   "all"    - re-tighten zd/zg to the running overlap of all members.
// Output: {start, end, ZD, ZG, n} per center.
package com.minustwo.chanlun;

import java.util.ArrayList;
import java.util.List;

import com.minustwo.chanlun.Types.Center;
import com.minustwo.chanlun.Types.Element;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Value;

public final class Zhongshu {

    private Zhongshu() {}

    public static List<Center> zhongshu(List<Element> els, String zone) {
        List<Center> centers = new ArrayList<>();
        int n = els.size();
        int i = 0;
        while (i + 2 < n) {
            long ZD = Math.max(Math.max(els.get(i).lo(), els.get(i + 1).lo()), els.get(i + 2).lo());
            long ZG = Math.min(Math.min(els.get(i).hi(), els.get(i + 1).hi()), els.get(i + 2).hi());
            if (ZD <= ZG) {
                List<Integer> members = new ArrayList<>();
                members.add(i);
                members.add(i + 1);
                members.add(i + 2);
                long zd = ZD, zg = ZG;
                int j = i + 3;
                while (j < n && els.get(j).lo() <= zg && els.get(j).hi() >= zd) {
                    members.add(j);
                    if ("all".equals(zone)) {
                        zd = Math.max(zd, els.get(j).lo());
                        zg = Math.min(zg, els.get(j).hi());
                    }
                    j++;
                }
                int last = members.get(members.size() - 1);
                centers.add(new Center(i, last, ZD, ZG, members.size()));
                i = last + 1;
            } else {
                i++;
            }
        }
        return centers;
    }

    // ==== Value tree adapters ===============================================

    public static List<Element> elementsFromValue(Value v) {
        List<Value> arr = v.mustArr();
        List<Element> out = new ArrayList<>(arr.size());
        for (Value e : arr) {
            OrderedObject o = e.mustObj();
            out.add(new Element(
                o.get("idx").mustInt(),
                o.get("lo").mustInt(),
                o.get("hi").mustInt()));
        }
        return out;
    }

    public static Value elementsToValue(List<Element> els) {
        List<Value> out = new ArrayList<>(els.size());
        for (Element el : els) {
            OrderedObject o = new OrderedObject();
            o.set("idx", Value.ofInt(el.idx()));
            o.set("lo", Value.ofInt(el.lo()));
            o.set("hi", Value.ofInt(el.hi()));
            out.add(Value.ofObject(o));
        }
        return Value.ofArray(out);
    }

    public static Value centersToValue(List<Center> cs) {
        List<Value> out = new ArrayList<>(cs.size());
        for (Center c : cs) {
            OrderedObject o = new OrderedObject();
            o.set("start", Value.ofInt(c.start()));
            o.set("end", Value.ofInt(c.end()));
            o.set("ZD", Value.ofInt(c.ZD()));
            o.set("ZG", Value.ofInt(c.ZG()));
            o.set("n", Value.ofInt(c.n()));
            out.add(Value.ofObject(o));
        }
        return Value.ofArray(out);
    }

    /** Parse trend_type's input: a list of centers, possibly carrying just
     *  {ZD, ZG} (start/end/n default to 0). */
    public static List<Center> centersFromValue(Value v) {
        List<Value> arr = v.mustArr();
        List<Center> out = new ArrayList<>(arr.size());
        for (Value e : arr) {
            OrderedObject o = e.mustObj();
            long start = o.has("start") ? o.get("start").mustInt() : 0;
            long end = o.has("end") ? o.get("end").mustInt() : 0;
            long n = o.has("n") ? o.get("n").mustInt() : 0;
            out.add(new Center(start, end, o.get("ZD").mustInt(), o.get("ZG").mustInt(), n));
        }
        return out;
    }
}
