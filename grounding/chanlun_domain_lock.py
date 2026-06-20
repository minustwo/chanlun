"""缠论 residua domain-lock 收口 — declare a LockObligation per chanlun 分型 residua-Scheme program.

What this is (the cross-domain 收口 over the chanlun 分型 residua-Scheme vocabulary)
----------------------------------------------------------------------------------
`grounding/chanlun_residua.py` defines `PRIMS = {name: (scheme_src, env)}` — the 缠论 Def-3 分型
detectors written as residua-Scheme programs, each carrying a content-`q` (the proof key: recompute
=> verify-without-trust). Separately, `lean/Chanlun/Fractal.lean` PROVES what each Def-3 concept IS
(the `isTopFractal` / `isBottomFractal` / `isInclusionNormalized` predicates).

To claim a residua-program "implements" its Lean concept, the lock the user actually wants is the
Lean theorem  `∀ inputs, evalL(program, inputs) = isX_lean(inputs)`  — discharged with `lake build`
(cc's Lean lane). Until that theorem's proof-q is recorded, the lock is an OPEN OBLIGATION, born
honestly `[domain_lock_undischarged]`. A diff-test passing / a produced value does NOT lock — only
a recorded Lean proof q does.

This module DECLARES that obligation for EVERY chanlun PRIM, binding each program's residua-Scheme
content-q to its `lean/Chanlun/Fractal.lean` target, so cc has a clear lake-discharge BACKLOG. It
mints nothing new: it composes residua's `apps/domain-lock/domain_lock.py` (declare / verify_lock /
discharge) over `chanlun_residua.PRIMS` (imported, NOT copied — the formulas stay single-sourced).

The TEMPLATE (already proven end-to-end by cc, separate lane)
------------------------------------------------------------
cc proved the umos-nq ICT Tier-A locks end-to-end on `lean/ICT/` with `lake` (e.g.
`evalL_eq_isBodyRatioAdmit`). That is the discharged shape. The N obligations declared here are the
chanlun BACKLOG cc discharges the SAME way: author the LOCK THEOREM over `lean/Chanlun/Fractal.lean`
(`evalL(program) ≡ isX`), `lake build`, then `domain_lock.discharge(ob, lean_proof_q)`.

The lock-theorem shape for chanlun (recorded in each obligation's note)
----------------------------------------------------------------------
chanlun's `isTopFractal` / `isBottomFractal` / `isInclusionNormalized` are **Prop** (not a Bool
`isX`). So the lock theorem is an `↔` — `evalL(program) = true ↔ isX` — the umos-nq Tier-B shape,
NOT a bare Bool `=`. Every obligation here records that ("Prop target; lock theorem is `↔`").

Every chanlun obligation here is `undischarged` (no lake proof yet — only the SHAPE is fixed). The
honesty assertion in `--status` proves it: a produced value is NOT a lock.

Run:
  python3 grounding/chanlun_domain_lock.py --status   # every PRIM, tier, ref, honest status
"""
import os
import sys

# Resolve residua the SAME way grounding/chanlun_residua.py does (os.path.expanduser('~/residua') —
# a logical home path, never a hard-coded machine path). Add the domain-lock app alongside src.
R = os.path.expanduser("~/residua")
for p in (f"{R}/src", f"{R}/apps/domain-lock"):
    if p not in sys.path:
        sys.path.insert(0, p)

# domain_lock self-bootstraps residua's import surface (from residua.appkit import bootstrap);
# importing it from this dir is enough once {R}/apps/domain-lock is on the path.
try:
    import domain_lock as DL  # residua apps/domain-lock — declare / verify_lock / discharge
except Exception as e:  # noqa: BLE001 — a missing/broken residua import is a transport fault; surface loudly
    raise SystemExit(
        f"[chanlun_domain_lock] cannot import residua domain_lock from {R}/apps/domain-lock: "
        f"{type(e).__name__}: {e}\n"
        f"  (residua must be on {R}; see grounding/chanlun_residua.py for the same resolution.)"
    )

# Reuse the chanlun 分型 residua-Scheme programs single-sourced from chanlun_residua.PRIMS (import,
# never copy — the formulas stay single-sourced and mirror Fractal.lean exactly).
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chanlun_residua  # noqa: E402 — same-dir sibling; provides PRIMS = {name: (scheme_src, env)}

DOMAIN = "chanlun"

# The discharged TEMPLATE (cc, separate lane: the umos-nq ICT Tier-A locks proven end-to-end with
# lake) — recorded here as the shape the chanlun backlog follows. The chanlun targets are Prop, so
# the lock theorem is the umos-nq Tier-B `↔` shape (`evalL = true ↔ isX`), not a bare Bool `=`.
TEMPLATE_NOTE = ("cc proved the umos-nq ICT Tier-A locks end-to-end with lake (e.g. "
                 "evalL_eq_isBodyRatioAdmit); these chanlun obligations are the lake-discharge "
                 "backlog, same loop, second theory.")

# ---------------------------------------------------------------------------
# The mapping: PRIM name -> (tier, lean_ref, note).
# VERIFIED against lean/Chanlun/Fractal.lean (def names + Prop-vs-Bool checked, NOT fabricated).
# All three chanlun Def-3 predicates are Prop -> Tier B (lock theorem is `evalL = true ↔ isX`).
# ---------------------------------------------------------------------------
MAPPING = {
    # ---- Tier B: Prop target (lock theorem evalL = true ↔ isX, an `↔`, the umos-nq Tier-B shape) ----
    "top_fractal": (
        "B", "chanlun:lean/Chanlun/Fractal.lean#isTopFractal",
        "Prop (b.h>a.h ∧ b.h>c.h ∧ b.l>a.l ∧ b.l>c.l); lock theorem is ↔ not =",
    ),
    "bottom_fractal": (
        "B", "chanlun:lean/Chanlun/Fractal.lean#isBottomFractal",
        "Prop (b.l<a.l ∧ b.l<c.l ∧ b.h<a.h ∧ b.h<c.h); ↔",
    ),
    "inclusion_normalized": (
        "B", "chanlun:lean/Chanlun/Fractal.lean#isInclusionNormalized",
        "Prop (the 包含关系 [chanlun_inclusion_precondition] Def-3 assumes upstream); ↔",
    ),
    # ---- 笔 新笔 SEPARATION KERNEL — the audited δmin fix, HONESTLY kernel-scoped (NOT full IsValidBi) ----
    # The residua-Scheme detector `(>= (abs (- pb pt)) 4)` mirrors chanlun_bi_kline_rule_grounding's
    # proven 新笔 math (新笔 ⟺ |p_b − p_t| ≥ 4) — the audited fix for the runtime δmin=1 bug. The Lean
    # target StrokeUniqueness.lean#IsValidBi is LIST-STRUCTURAL (over `List Fractal`); this 2-pivot
    # detector captures only its δmin SEPARATION CLAUSE (the `f.idx − a.idx ≥ δmin` gate of the
    # opposite-far branch in IsValidBi_from / Stroke.step), NOT the full list validity. The lock
    # theorem cc will prove is the separation-clause direction (evalL = true ↔ the δmin gate holds),
    # NOT full IsValidBi. The full list-decomposition lock remains a discovered residue R4.
    "bi_separation": (
        "B", "chanlun:lean/Chanlun/StrokeUniqueness.lean#IsValidBi",
        "Prop, SEPARATION KERNEL of 新笔 (the δmin clause `f.idx−a.idx ≥ δmin`, here δmin=4 ⟺ "
        "|p_b−p_t|≥4 — the audited δmin=1-bug fix), NOT full IsValidBi list validity (= R4, "
        "list-structural over List Fractal); lock theorem is the separation-clause ↔, not full =",
    ),
}


def build_obligations():
    """Declare a LockObligation per chanlun PRIM (a real domain_lock.declare, born undischarged).
    Returns a list of (name, tier, kind, payload) where kind == 'obligation' (payload is a
    LockObligation) — or 'intent' for an honest unliftable surface (a real fault, never a fake lock).

    Every obligation is born `undischarged` — NONE is locked (honest: no lake proof exists yet)."""
    out = []
    for name, (scheme_src, _env) in chanlun_residua.PRIMS.items():
        tier, lean_ref, note = MAPPING.get(name, ("B", None, "unmapped — no Lean target"))
        if lean_ref is None:
            # No mapped Lean ref — surface it as an intent (no fabricated ref), never a fake lock.
            out.append((name, tier, "intent", {
                "name": name, "tier": tier, "isX_lean_ref": None,
                "status": "no_lean_target", "locked": False,
                "residue": "[chanlun_no_lean_target]", "note": note,
            }))
            continue
        # A real lock obligation, born undischarged. declare() raises ProgramNotLiftable on a
        # malformed program — a real fault we surface rather than fabricate a lock over.
        try:
            ob = DL.declare(scheme_src, DOMAIN, name, lean_ref)
        except DL.ProgramNotLiftable as e:
            out.append((name, tier, "intent", {
                "name": name, "tier": tier, "isX_lean_ref": lean_ref,
                "status": "unliftable", "locked": False,
                "residue": f"[chanlun_program_not_liftable: {e}]", "note": note,
            }))
            continue
        out.append((name, tier, "obligation", ob))
    return out


def _status_rows():
    """Yield (name, tier, ref_str, status_str, residue_str) for --status, asserting honesty:
    every real obligation verifies as undischarged + [domain_lock_undischarged] (NOT locked)."""
    rows = []
    for name, tier, kind, payload in build_obligations():
        if kind == "intent":
            ref = payload.get("isX_lean_ref") or "NONE"
            rows.append((name, tier, ref, payload["status"], payload["residue"]))
            continue
        ob = payload
        st = DL.verify_lock(ob)
        # HONESTY ASSERTION: a freshly declared chanlun obligation MUST be undischarged + residue.
        assert ob.status == "undischarged" and ob.lean_proof_q is None, \
            f"{name}: expected born-undischarged, got status={ob.status} proof_q={ob.lean_proof_q}"
        assert (not st.locked) and st.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
            f"{name}: expected [domain_lock_undischarged], got locked={st.locked} residue={st.residue}"
        rows.append((name, tier, ob.isX_lean_ref, ob.status, st.residue))
    return rows


def main(argv):
    if len(argv) >= 2 and argv[1] == "--status":
        rows = _status_rows()
        print(f"# chanlun (缠论) residua domain-lock 收口 — {len(rows)} obligations over "
              f"chanlun_residua.PRIMS")
        print(f"# TEMPLATE: {TEMPLATE_NOTE}")
        print(f"# Lock-theorem shape: chanlun isX are Prop -> evalL = true ↔ isX (Tier-B ↔, not Bool =).")
        print(f"# Kernel-scope: bi_separation locks the 新笔 SEPARATION KERNEL (the δmin clause, "
              f"δmin=4 ⟺ |p_b−p_t|≥4 — the audited δmin=1-bug fix), NOT full IsValidBi list validity (= R4).")
        print(f"# {'PRIM':22s} {'TIER':4s} {'STATUS':16s} {'LEAN_REF (or NONE)'}")
        per_tier = {}
        for name, tier, ref, status, residue in rows:
            per_tier[tier] = per_tier.get(tier, 0) + 1
            scope = "  [kernel: 新笔 δmin separation clause, NOT full IsValidBi = R4]" if name == "bi_separation" else ""
            print(f"  {name:22s} {tier:4s} {status:16s} {ref}{scope}")
        tiers = ", ".join(f"{t}={per_tier.get(t, 0)}" for t in ("A", "B", "C", "D") if per_tier.get(t))
        print(f"# SUMMARY: {len(rows)} obligations declared, ALL undischarged "
              f"(no lake proof yet — honest). Tiers: {tiers}.")
        print(f"# A produced value does NOT lock; only a recorded lake proof-q discharges an "
              f"obligation (cc's lane). This is the cross-domain proof: residua-Scheme + domain-lock "
              f"span 缠论 (a SECOND theory), realizing the 多理论共存 thesis.")
        return 0

    print("usage: python3 grounding/chanlun_domain_lock.py --status", file=sys.stderr)
    print("  (declares a residua domain-lock obligation per chanlun 分型 primitive, born undischarged)",
          file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
