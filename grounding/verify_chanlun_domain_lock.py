"""Verifier for grounding/chanlun_domain_lock.py — §15 mutant-FIRST, §40 anti-vacuity.

§15 mutant-FIRST (run BEFORE anything else — a seal that can't fail seals nothing):
  The chanlun author's status-quo FOOTGUN is "my residua-Scheme 分型 program RAN and produced a
  value, therefore it's LOCKED to my Lean isTopFractal". An OUTPUT is not a PROOF. The mutant here
  is a NAIVE "lock" that reports a PRIM **locked** because its `chanlun_residua.run()` produced a
  (non-residue) value. The REAL `domain_lock.verify_lock` reports `[domain_lock_undischarged]` for
  the SAME obligation (a produced value does NOT discharge it — only a recorded Lean proof q does).
  mutant-reports-locked  ↔  real-reports-undischarged.

§15 (bi_separation) — the mutant is the REAL AUDITED δmin=1 RUNTIME BUG:
  For the 新笔 SEPARATION KERNEL, the mutant is NOT a synthetic footgun — it is the actual audited
  runtime bug `δmin=1` (`(>= (abs (- pb pt)) 1)`), the gate chanlun_bi_kline_rule_grounding PROVED
  diverges from 缠论. At a pivot separation of 3 (and 1, 2) the δ=1 mutant ADMITS a 新笔 (顶/底分型
  that share K-lines / have <3 K-lines between extremes — an INVALID 笔), while the faithful δ=4
  detector `(>= ... 4)` REFUSES it. mutant-admits(sep=3) ↔ real-refuses(sep=3) on the SAME pivot
  pair directly encodes the audit FIX (δmin: 1 → 4). The value-≠-proof §15 (a produced value does
  NOT lock) ALSO applies to the bi_separation obligation: even the faithful detector's `true` output
  reports [domain_lock_undischarged], not locked.

§40 anti-vacuity (the gate is not a blanket reject):
  A DISCHARGED obligation reports `locked`. Demonstrated on a COPY of a real obligation:
  `discharge(ob, "<stub_proof_q>")` -> status `discharged` / locked (proving the discharge path is
  REACHABLE — the residue isn't vacuous), WHILE asserting the REAL chanlun obligations stay
  `undischarged` (no stub is used for them). Also: a TAMPERED scheme_src (program-q mismatch)
  RE-OPENS a discharged lock.

Run:  python3 grounding/verify_chanlun_domain_lock.py
"""
import dataclasses
import sys

import chanlun_domain_lock as L
import chanlun_residua  # the single source of the chanlun 分型 residua-Scheme programs


DL = L.DL


def _is_residue_value(val):
    """The residua convention: a `(residue n)` output. A naive 'it produced a value' test treats
    anything that is NOT a residue as a 'pass'. (val shapes are JSON dicts with a 'tag'.)"""
    return isinstance(val, dict) and val.get("tag") == "residue"


def naive_value_reports_locked(name):
    """The §15 MUTANT — the chanlun status quo. 'Lock' a PRIM because its residua-Scheme 分型
    program RAN and produced a (non-residue) value. An output is NOT a proof; this silently reports
    an UNPROVEN program as locked. Returns True iff the program produced a non-residue value."""
    scheme_src, env = chanlun_residua.PRIMS[name]
    val, _q = chanlun_residua.run(scheme_src, env)
    return not _is_residue_value(val)  # the bug: a produced value is treated as a lock


def section_15_mutant_first():
    """§15 — RUN FIRST. The mutant (a produced value) reports LOCKED; the real mechanism reports
    [domain_lock_undischarged] for the SAME obligation. Asserted over the top_fractal PRIM, which
    has a real Lean ref + a producing program."""
    name = "top_fractal"  # Tier B, runs, produces a list value (not a residue)
    _tier, lean_ref, _note = L.MAPPING[name]
    scheme_src = chanlun_residua.PRIMS[name][0]

    # the mutant: "it produced a value -> locked"
    mutant_locked = naive_value_reports_locked(name)
    assert mutant_locked is True, (
        "§15 precondition: the naive 'produced a value' path must report LOCKED for top_fractal "
        "(the silent false-lock the real mechanism exists to catch).")

    # the real mechanism: the SAME obligation is undischarged + carries the residue.
    ob = DL.declare(scheme_src, L.DOMAIN, name, lean_ref)
    st = DL.verify_lock(ob)
    assert ob.status == "undischarged" and ob.lean_proof_q is None, \
        f"§15: obligation must be born undischarged, got {ob.status}/{ob.lean_proof_q}"
    assert (not st.locked) and st.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§15: real mechanism must report [domain_lock_undischarged], got {st}"

    # the contrast IS the point: mutant-locked XOR real-locked.
    assert mutant_locked != st.locked, \
        "§15: mutant-reports-locked must contradict real-reports-undischarged (the seal is real)."
    print("§15 mutant-first PASS: a produced value reports LOCKED (mutant); the real mechanism "
          "reports [domain_lock_undischarged] for the SAME obligation — a value is not a proof.")


def section_40_anti_vacuity():
    """§40 — the gate is NOT a blanket reject. A DISCHARGED obligation (stub proof q) reports
    locked on a COPY; the REAL chanlun obligations stay undischarged (no stub used). A TAMPERED
    program re-opens a discharged lock."""
    name = "bottom_fractal"  # Tier B real obligation
    scheme_src = chanlun_residua.PRIMS[name][0]
    _, lean_ref, _ = L.MAPPING[name]
    ob = DL.declare(scheme_src, L.DOMAIN, name, lean_ref)

    # the REAL obligation stays undischarged (we never stub-discharge it).
    st_real = DL.verify_lock(ob)
    assert (not st_real.locked) and st_real.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§40: the REAL chanlun obligation must stay undischarged, got {st_real}"

    # on a COPY: a stub proof q discharges it -> locked (the discharge path is REACHABLE).
    stub_proof_q = "stub_lean_proof_q_for_anti_vacuity_only"
    discharged = DL.discharge(ob, stub_proof_q)  # returns a NEW frozen obligation (ob unchanged)
    assert discharged.status == "discharged" and discharged.lean_proof_q == stub_proof_q, \
        f"§40: discharge must record the proof q + flip status, got {discharged}"
    st_locked = DL.verify_lock(discharged)
    assert st_locked.locked and st_locked.residue is None, \
        f"§40: a discharged obligation (proof q + matching program_q) must report locked, got {st_locked}"

    # the original is still undischarged (discharge is non-mutating — proves no stub leaked back).
    assert DL.verify_lock(ob).residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        "§40: discharging a copy must NOT lock the original chanlun obligation."

    # TAMPER: a structurally-different program no longer matches program_q -> the lock RE-OPENS.
    # Weaken the bottom-fractal first strict `<` to `<=` — a genuinely different Def-3 body. (The
    # interior bar is inlined as `(unwrap (first (drop w 1)))`, so match that exact conjunct.)
    tampered_src = scheme_src.replace(
        "(< (field (unwrap (first (drop w 1))) l) (field (unwrap (first w)) l))",
        "(<= (field (unwrap (first (drop w 1))) l) (field (unwrap (first w)) l))", 1)
    assert tampered_src != scheme_src, \
        "§40 precondition: the tamper must actually change the source."
    assert DL.program_q(tampered_src) != discharged.program_q, \
        "§40 precondition: a tampered program must have a DIFFERENT content-q (else binding is vacuous)."
    tampered = dataclasses.replace(discharged, program_src=tampered_src)
    st_tamper = DL.verify_lock(tampered)
    assert (not st_tamper.locked) and st_tamper.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§40 anti-vacuity: a TAMPERED discharged lock must RE-OPEN [domain_lock_undischarged], got {st_tamper}"

    print("§40 anti-vacuity PASS: a discharged obligation (stub proof q, on a COPY) reports locked; "
          "the REAL chanlun obligations stay undischarged; a TAMPERED program re-opens the lock.")


def section_all_undischarged():
    """Full vocabulary: every Tier-B obligation is born undischarged + residue. No PRIM is locked."""
    obs = L.build_obligations()
    assert len(obs) == len(chanlun_residua.PRIMS), \
        f"every PRIM must yield an obligation/intent: {len(obs)} vs {len(chanlun_residua.PRIMS)}"
    n_undischarged = 0
    for name, _tier, kind, payload in obs:
        if kind == "obligation":
            st = DL.verify_lock(payload)
            assert payload.status == "undischarged", f"{name}: must be undischarged"
            assert (not st.locked) and st.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
                f"{name}: must carry [domain_lock_undischarged], got {st}"
            n_undischarged += 1
        else:  # an honest unliftable / no-target intent — no Lean lock, never locked.
            assert payload["locked"] is False, f"{name}: an intent must never be locked"
    assert n_undischarged == len(chanlun_residua.PRIMS), \
        f"all {len(chanlun_residua.PRIMS)} chanlun PRIMs must be real undischarged obligations, got {n_undischarged}"
    print(f"full vocabulary PASS: {len(obs)} PRIMs -> {n_undischarged} undischarged obligations. "
          f"NONE locked (honest — no lake proof yet).")


# The audited runtime BUG (δmin=1) and the faithful FIX (δmin=4), as residua-Scheme separation
# gates over the SAME 2-pivot env. `bi_separation` IS the faithful δ=4 detector (single-sourced).
_REAL_FIX_SRC = chanlun_residua.PRIMS["bi_separation"][0]                # (>= (abs (- pb pt)) 4)
_MUTANT_BUG_SRC = _REAL_FIX_SRC.replace(") 4)", ") 1)", 1)               # (>= (abs (- pb pt)) 1) — δmin=1


def section_15_bi_separation_delta_bug():
    """§15 (bi_separation) — the mutant is the REAL audited δmin=1 runtime bug. On the SAME pivot
    pair at separation=3 (no shared K-lines, but only 2 K-lines between extremes → NOT a 新笔), the
    δ=1 BUG admits the 笔 while the faithful δ=4 FIX refuses it. This directly encodes the audit fix
    (δmin: 1 → 4). PLUS value-≠-proof: even the faithful detector's `true` does NOT lock."""
    # Sanity: the mutant must actually be the δ=1 gate (a real, different program).
    assert _MUTANT_BUG_SRC == "(>= (abs (- pb pt)) 1)", \
        f"§15 precondition: the δmin=1 bug src must be the runtime gate, got {_MUTANT_BUG_SRC!r}"
    assert _MUTANT_BUG_SRC != _REAL_FIX_SRC, "§15 precondition: bug and fix must be different programs."

    # The audit boundary: pivot separation = 3 (the WLOG p_t<p_b pair pt=0, pb=3). Per the proven
    # math (chanlun_bi_kline_rule_grounding), this is NOT a 新笔 (only 2 K-lines between extremes).
    env_invalid = {"pt": 0, "pb": 3}
    bug_v, _ = chanlun_residua.run(_MUTANT_BUG_SRC, env_invalid)   # δ=1 admits it (the BUG)
    fix_v, _ = chanlun_residua.run(_REAL_FIX_SRC, env_invalid)     # δ=4 refuses it (the FIX)
    assert bug_v == {"tag": "bool", "b": True}, \
        f"§15: the δmin=1 BUG must ADMIT the invalid 新笔 at separation=3, got {bug_v}"
    assert fix_v == {"tag": "bool", "b": False}, \
        f"§15: the faithful δmin=4 FIX must REFUSE the invalid 新笔 at separation=3, got {fix_v}"
    assert bug_v != fix_v, \
        "§15: mutant(δ=1)-admits must contradict real(δ=4)-refuses at separation=3 (the audit fix)."

    # The bug admits at sep=1,2,3 (all invalid 新笔); the fix refuses all three — the whole bug band.
    for sep in (1, 2, 3):
        bv, _ = chanlun_residua.run(_MUTANT_BUG_SRC, {"pt": 0, "pb": sep})
        fv, _ = chanlun_residua.run(_REAL_FIX_SRC, {"pt": 0, "pb": sep})
        assert bv["b"] is True and fv["b"] is False, \
            f"§15: at separation={sep} the δ=1 bug must admit and the δ=4 fix refuse, got bug={bv} fix={fv}"
    # At the faithful boundary (sep=4) BOTH agree (a genuine 新笔) — the fix is not a blanket reject.
    bv4, _ = chanlun_residua.run(_MUTANT_BUG_SRC, {"pt": 0, "pb": 4})
    fv4, _ = chanlun_residua.run(_REAL_FIX_SRC, {"pt": 0, "pb": 4})
    assert bv4["b"] is True and fv4["b"] is True, \
        f"§15: at separation=4 (a real 新笔) both gates must admit, got bug={bv4} fix={fv4}"

    # value-≠-proof: even the FAITHFUL detector's produced `true` (at sep=4) does NOT lock. The
    # SAME obligation reports [domain_lock_undischarged] — a value is not a proof (the §15 invariant).
    _tier, lean_ref, _note = L.MAPPING["bi_separation"]
    ob = DL.declare(_REAL_FIX_SRC, L.DOMAIN, "bi_separation", lean_ref)
    st = DL.verify_lock(ob)
    assert ob.status == "undischarged" and ob.lean_proof_q is None, \
        f"§15: bi_separation obligation must be born undischarged, got {ob.status}/{ob.lean_proof_q}"
    assert (not st.locked) and st.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§15: faithful detector value must NOT lock — expected [domain_lock_undischarged], got {st}"
    # Kernel-scope honesty: the obligation ref is StrokeUniqueness#IsValidBi (the separation KERNEL,
    # NOT the full list-structural validity — R4).
    assert ob.isX_lean_ref.endswith("StrokeUniqueness.lean#IsValidBi"), \
        f"§15: bi_separation must lock to the StrokeUniqueness IsValidBi target, got {ob.isX_lean_ref}"
    print("§15 (bi_separation) PASS: the mutant IS the REAL audited δmin=1 runtime bug — it ADMITS "
          "an invalid 新笔 at separation=1,2,3 (shared K-lines / <3 between extremes) while the "
          "faithful δ=4 detector REFUSES them (the audit fix δmin: 1 → 4); both admit a real 新笔 at "
          "separation=4. And value≠proof: the faithful detector's `true` reports "
          "[domain_lock_undischarged], NOT locked (kernel-scoped to IsValidBi, not full list validity = R4).")


# The 笔-DECOMPOSITION program (R4) and its δmin=1 over-segmentation MUTANT, as residua-Scheme folds
# over the SAME fixed `List Fractal`. `bi_decomposition` IS the faithful δ=4 fold (single-sourced);
# the mutant replaces the opposite-far emit gate `≥ 4` with the audited buggy `≥ 1`.
_REAL_DECOMP_SRC = chanlun_residua.PRIMS["bi_decomposition"][0]            # δmin=4 opposite-far gate
_MUTANT_DECOMP_SRC = _REAL_DECOMP_SRC.replace(
    "(>= (- (field f idx) (field a idx)) 4)",
    "(>= (- (field f idx) (field a idx)) 1)", 1)                           # δmin=1 — the audited bug


def _decode_strokes(val):
    """Decode a residua list-of-stroke-records value into [{from_idx,to_idx,dir}, …] (plain ints)."""
    assert isinstance(val, dict) and val.get("tag") == "list", f"expected a list value, got {val}"
    out = []
    for rec in val["xs"]:
        assert rec.get("tag") == "record", f"expected stroke records, got {rec}"
        out.append({kv[0]: kv[1]["n"] for kv in rec["kvs"]})
    return out


def _min_separation(strokes):
    """The smallest 笔 separation `to_idx − from_idx` in a decomposition (∞ for the empty 笔 list)."""
    return min((s["to_idx"] - s["from_idx"] for s in strokes), default=float("inf"))


def section_15_bi_decomposition_oversegment():
    """§15 (bi_decomposition) — the mutant is the δmin=1 over-segmentation of the FULL fold. On the
    SAME fixed `List Fractal`, the δ=1 BUG emits a 笔 ⟨6,8⟩ (separation 2 — only 2 K-lines between
    extremes, an INVALID 笔 `IsValidBi … 4` REJECTS), where the faithful δ=4 FOLD instead extends to
    ⟨6,12⟩ (separation 6 — a real 新笔). The δ=1 decomposition is OVER-SEGMENTED and IsValidBi-invalid
    at δ=4; the δ=4 decomposition is the unique valid 笔. value-≠-proof ALSO holds: even the faithful
    fold's produced 笔 list reports [domain_lock_undischarged] — a produced decomposition is NOT a lock."""
    # Sanity: the mutant must actually be the δ=1 opposite-far gate (a real, different program).
    assert _MUTANT_DECOMP_SRC != _REAL_DECOMP_SRC, \
        "§15 precondition: the δ=1 over-segmentation mutant must differ from the faithful δ=4 fold."
    assert "(>= (- (field f idx) (field a idx)) 1)" in _MUTANT_DECOMP_SRC, \
        "§15 precondition: the mutant must use the audited δmin=1 emit gate."

    faithful = _decode_strokes(chanlun_residua.run(_REAL_DECOMP_SRC, None)[0])
    oversegmented = _decode_strokes(chanlun_residua.run(_MUTANT_DECOMP_SRC, None)[0])

    # The faithful δ=4 decomposition is the unique valid 笔 list = strokes frs 4 = the IsValidBi alt.
    assert faithful == [{"from_idx": 2, "to_idx": 6, "dir": 2},
                        {"from_idx": 6, "to_idx": 12, "dir": 1}], \
        f"§15: the faithful δ=4 fold must emit the unique 笔 [⟨2,6,down⟩,⟨6,12,up⟩], got {faithful}"
    # The δ=1 BUG over-segments: it emits ⟨6,8⟩ (separation 2) instead of extending to ⟨6,12⟩.
    assert oversegmented == [{"from_idx": 2, "to_idx": 6, "dir": 2},
                             {"from_idx": 6, "to_idx": 8, "dir": 1}], \
        f"§15: the δ=1 BUG must over-segment to [⟨2,6,down⟩,⟨6,8,up⟩], got {oversegmented}"
    assert faithful != oversegmented, \
        "§15: the δ=4 decomposition must differ from the δ=1 over-segmentation (the bug is real)."

    # The structural verdict: the δ=1 decomposition contains a 笔 with separation < δmin=4 — so
    # `IsValidBi frs 4` (which requires every opposite-far emit to satisfy `f.idx−a.idx ≥ 4`) REJECTS
    # it. The faithful δ=4 decomposition has every 笔 ≥ 4 — IsValidBi at δ=4 accepts it.
    assert _min_separation(oversegmented) < 4, \
        f"§15: the δ=1 over-segmentation must contain a 笔 with separation < 4 (IsValidBi-invalid), " \
        f"got min separation {_min_separation(oversegmented)}"
    assert _min_separation(faithful) >= 4, \
        f"§15: the faithful δ=4 decomposition must have every 笔 separation ≥ 4 (IsValidBi-valid), " \
        f"got min separation {_min_separation(faithful)}"

    # value-≠-proof: even the FAITHFUL fold's produced 笔 list does NOT lock. The SAME obligation
    # reports [domain_lock_undischarged] — a produced decomposition is not a proof (the §15 invariant).
    _tier, lean_ref, _note = L.MAPPING["bi_decomposition"]
    ob = DL.declare(_REAL_DECOMP_SRC, L.DOMAIN, "bi_decomposition", lean_ref)
    st = DL.verify_lock(ob)
    assert ob.status == "undischarged" and ob.lean_proof_q is None, \
        f"§15: bi_decomposition obligation must be born undischarged, got {ob.status}/{ob.lean_proof_q}"
    assert (not st.locked) and st.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§15: a produced 笔 decomposition must NOT lock — expected [domain_lock_undischarged], got {st}"
    # R4-closure honesty: the obligation locks to StrokeUniqueness#IsValidBi (the FULL list validity).
    assert ob.isX_lean_ref.endswith("StrokeUniqueness.lean#IsValidBi"), \
        f"§15: bi_decomposition must lock to the StrokeUniqueness IsValidBi target, got {ob.isX_lean_ref}"
    print("§15 (bi_decomposition) PASS: the mutant is the δmin=1 OVER-SEGMENTATION of the full fold — "
          "on the SAME `List Fractal` it emits a 笔 ⟨6,8⟩ (separation 2, IsValidBi-INVALID at δ=4) "
          "where the faithful δ=4 fold extends to ⟨6,12⟩ (a real 新笔); the δ=4 decomposition is the "
          "unique IsValidBi-valid 笔. And value≠proof: the faithful fold's produced 笔 list reports "
          "[domain_lock_undischarged], NOT locked (R4 — full list-structural validity, not a kernel).")


def section_40_bi_decomposition():
    """§40 (bi_decomposition) — the discharge path is REACHABLE for the R4 obligation (stub proof q on
    a COPY → locked) while the REAL bi_decomposition obligation stays undischarged. The faithful fold
    produces a non-vacuous 笔 list AND the obligation is reachably dischargeable yet undischarged."""
    _tier, lean_ref, _note = L.MAPPING["bi_decomposition"]
    ob = DL.declare(_REAL_DECOMP_SRC, L.DOMAIN, "bi_decomposition", lean_ref)

    # the faithful fold produces a non-vacuous 笔 list (two strokes) — non-vacuous.
    strokes = _decode_strokes(chanlun_residua.run(_REAL_DECOMP_SRC, None)[0])
    assert len(strokes) == 2, f"§40 precondition: bi_decomposition must emit 2 strokes, got {strokes}"

    # the REAL obligation stays undischarged (we never stub-discharge it).
    st_real = DL.verify_lock(ob)
    assert (not st_real.locked) and st_real.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§40: the REAL bi_decomposition obligation must stay undischarged, got {st_real}"

    # on a COPY: a stub proof q discharges the R4 obligation → locked (path REACHABLE).
    stub_proof_q = "stub_lean_proof_q_bi_decomposition_R4_anti_vacuity_only"
    discharged = DL.discharge(ob, stub_proof_q)
    st_locked = DL.verify_lock(discharged)
    assert discharged.status == "discharged" and st_locked.locked and st_locked.residue is None, \
        f"§40: a stub-discharged bi_decomposition copy must report locked, got {discharged.status}/{st_locked}"
    # the original R4 obligation is still undischarged (non-mutating discharge).
    assert DL.verify_lock(ob).residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        "§40: discharging a copy must NOT lock the REAL bi_decomposition obligation."
    print("§40 (bi_decomposition) PASS: the faithful fold emits a non-vacuous 笔 list AND the R4 "
          "obligation's discharge path is REACHABLE (stub proof q on a COPY → locked), while the REAL "
          "bi_decomposition obligation stays undischarged (no stub used — only cc's lake proof "
          "`IsValidBi frs 4 (evalL prog)` discharges it).")


def section_40_bi_separation():
    """§40 (bi_separation) — the discharge path is REACHABLE for the kernel obligation (stub proof q
    on a COPY → locked) while the REAL bi_separation obligation stays undischarged. sep=4 → the
    detector is true AND the obligation is reachably dischargeable yet undischarged for real."""
    _tier, lean_ref, _note = L.MAPPING["bi_separation"]
    ob = DL.declare(_REAL_FIX_SRC, L.DOMAIN, "bi_separation", lean_ref)

    # sep=4: the detector IS true (a real 新笔) — non-vacuous.
    v4, _ = chanlun_residua.run(_REAL_FIX_SRC, {"pt": 0, "pb": 4})
    assert v4 == {"tag": "bool", "b": True}, f"§40 precondition: bi_separation must be true at sep=4, got {v4}"

    # the REAL obligation stays undischarged (we never stub-discharge it).
    st_real = DL.verify_lock(ob)
    assert (not st_real.locked) and st_real.residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        f"§40: the REAL bi_separation obligation must stay undischarged, got {st_real}"

    # on a COPY: a stub proof q discharges the kernel obligation → locked (path REACHABLE).
    stub_proof_q = "stub_lean_proof_q_bi_separation_kernel_anti_vacuity_only"
    discharged = DL.discharge(ob, stub_proof_q)
    st_locked = DL.verify_lock(discharged)
    assert discharged.status == "discharged" and st_locked.locked and st_locked.residue is None, \
        f"§40: a stub-discharged bi_separation copy must report locked, got {discharged.status}/{st_locked}"
    # the original kernel obligation is still undischarged (non-mutating discharge).
    assert DL.verify_lock(ob).residue == DL.DOMAIN_LOCK_UNDISCHARGED, \
        "§40: discharging a copy must NOT lock the REAL bi_separation obligation."
    print("§40 (bi_separation) PASS: sep=4 → the detector is true AND the kernel obligation's "
          "discharge path is REACHABLE (stub proof q on a COPY → locked), while the REAL "
          "bi_separation obligation stays undischarged (no stub used).")


def main():
    # §15 FIRST — falsifiability before anything else.
    section_15_mutant_first()
    section_15_bi_separation_delta_bug()
    section_15_bi_decomposition_oversegment()
    section_40_anti_vacuity()
    section_40_bi_separation()
    section_40_bi_decomposition()
    section_all_undischarged()
    print("verify_chanlun_domain_lock: PASS — every chanlun (缠论) 分型 residua-Scheme primitive has "
          "a domain-lock obligation bound to its lean/Chanlun/Fractal.lean target, born honestly "
          "[domain_lock_undischarged] (a value is NOT a proof; §15). The discharge path is reachable "
          "(§40), the real obligations stay undischarged, and a tampered program re-opens the lock. "
          "This is the CROSS-DOMAIN proof: residua-Scheme + the domain-lock mechanism span a SECOND "
          "theory (缠论, not just ICT) — ICT / 缠论 as different admissibility gates on the same "
          "residua carrier (多理论共存). cc's lake lane is the discharge backlog.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
