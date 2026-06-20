"""Verifier for grounding/chanlun_domain_lock.py — §15 mutant-FIRST, §40 anti-vacuity.

§15 mutant-FIRST (run BEFORE anything else — a seal that can't fail seals nothing):
  The chanlun author's status-quo FOOTGUN is "my residua-Scheme 分型 program RAN and produced a
  value, therefore it's LOCKED to my Lean isTopFractal". An OUTPUT is not a PROOF. The mutant here
  is a NAIVE "lock" that reports a PRIM **locked** because its `chanlun_residua.run()` produced a
  (non-residue) value. The REAL `domain_lock.verify_lock` reports `[domain_lock_undischarged]` for
  the SAME obligation (a produced value does NOT discharge it — only a recorded Lean proof q does).
  mutant-reports-locked  ↔  real-reports-undischarged.

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


def main():
    # §15 FIRST — falsifiability before anything else.
    section_15_mutant_first()
    section_40_anti_vacuity()
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
