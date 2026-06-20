"""缠论 (Chan) 分型 (fractal) detectors, written as residua (Scheme) programs — the verified vocabulary.

Each is the executable detector (= our Lean `isX` predicate-mirror) expressed in residua's
cross-domain residue operators. Semantics = residua's Lean `evalL`; each carries a content hash
`q` (proof key: recompute => verify-without-trust; dedup key: same meaning => same q).
Formulas mirror `lean/Chanlun/Fractal.lean` EXACTLY — zero parameters, integer ticks (the Lean
`Bar` is `{ h : Int, l : Int }`; real-valued price expressed as integer ticks).

This is the chanlun analog of umos-nq `analysis/ict_residua.py`. It proves residua-Scheme spans a
SECOND theory (缠论, not just ICT): both theories are different admissibility gates (`a`) over the
same residua carrier (`q`). 数学才是唯一的判决 — the residua-Scheme body must mirror the Lean body
character-for-character, which is the whole point of the cross-domain lock.

Source of truth (NOT invented): `lean/Chanlun/Fractal.lean`, Definition 3 (分型), over a
3-bar interior window (a, b, c) where b is the middle (interior) bar:

    isTopFractal a b c    := b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l
    isBottomFractal a b c := b.l < a.l ∧ b.l < c.l ∧ b.h < a.h ∧ b.h < c.h
    isInclusionNormalized a b c :=
        ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) ∧ ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) ∧
        ¬ (c.h ≤ b.h ∧ c.l ≥ b.l) ∧ ¬ (b.h ≤ c.h ∧ b.l ≥ c.l)

`top_fractal` / `bottom_fractal` are the Def-3 a-gate (top ∨ bottom = the structural pivot);
`inclusion_normalized` is the `[chanlun_inclusion_precondition]` Def-3 assumes upstream.

Run:  python3 grounding/chanlun_residua.py
"""
import os
import sys
import json

# Resolve residua the SAME way umos-nq analysis/ict_residua.py does (os.path.expanduser('~/residua')
# — a logical home path, never a hard-coded machine path). chanlun grounding/ already references
# residua this way (grounding/chanlun_singlepass_idempotent_grounding.py). The tour shim _tourlib
# gives the SEALED scm->wire codec + the CLI run/q verbs in-process.
R = os.path.expanduser("~/residua")
sys.path[:0] = [f"{R}/src", f"{R}/examples/tour"]
import _tourlib as T  # noqa: E402 — residua tour shim (scm_to_wire / cli / program_json)

# ---------------------------------------------------------------------------
# Scheme♭ fragment builders. `and` in residua-Scheme is BINARY (a flat 4-arg `and` does NOT lift),
# so a 4-conjunct Def-3 body is written as nested binary `and` — same discipline as the umos-nq
# swing_high/swing_low programs. Bars are residua records with integer fields `h` / `l` (the Lean
# `Bar` fields). The 3-bar window pulls a (first), c (last), and the interior bar b via
# `(unwrap (first (drop w 1)))` — the EXACT mid-extraction the umos-nq swing detectors use.
# ---------------------------------------------------------------------------
_MID = "(unwrap (first (drop w 1)))"   # b — the interior (middle) bar of the 3-window
_A = "(unwrap (first w))"              # a — the left neighbour
_C = "(unwrap (last w))"               # c — the right neighbour


def _f(rec, field):
    return f"(field {rec} {field})"


def _and(x, y):
    return f"(and {x} {y})"


def _not(x):
    return f"(not {x})"


# --- 3-bar sample windows (records h/l) for the detectors -------------------
# Four bars -> two 3-windows. Chosen so the vocabulary is NON-VACUOUS: w0 is a TOP fractal,
# w1 is a BOTTOM fractal, and w0 is inclusion-normalized (a staircase, no adjacent containment).
#   b0 = (h100, l90)   b1 = (h130, l120)   b2 = (h95, l60)   b3 = (h115, l100)
#   w0 = (b0,b1,b2): mid=b1 is a TOP    (130>100,130>95,120>90,120>60)
#   w1 = (b1,b2,b3): mid=b2 is a BOTTOM (60<120,60<100,95<130,95<115)
BARS = """(append (singleton (record (h 100) (l 90)))
         (append (singleton (record (h 130) (l 120)))
         (append (singleton (record (h 95) (l 60)))
                 (singleton (record (h 115) (l 100))))))"""

# A 3-bar window with NO adjacent containment (staircase) — inclusion_normalized = true here.
WIN_NORMALIZED = """(append (singleton (record (h 100) (l 90)))
         (append (singleton (record (h 130) (l 120)))
                 (singleton (record (h 95) (l 60)))))"""


# --- Def-3 bodies, transcribed character-for-character from Fractal.lean ----
# isTopFractal a b c := b.h > a.h ∧ b.h > c.h ∧ b.l > a.l ∧ b.l > c.l
_TOP_BODY = _and(
    f"(> {_f(_MID, 'h')} {_f(_A, 'h')})",
    _and(
        f"(> {_f(_MID, 'h')} {_f(_C, 'h')})",
        _and(
            f"(> {_f(_MID, 'l')} {_f(_A, 'l')})",
            f"(> {_f(_MID, 'l')} {_f(_C, 'l')})",
        ),
    ),
)

# isBottomFractal a b c := b.l < a.l ∧ b.l < c.l ∧ b.h < a.h ∧ b.h < c.h
_BOTTOM_BODY = _and(
    f"(< {_f(_MID, 'l')} {_f(_A, 'l')})",
    _and(
        f"(< {_f(_MID, 'l')} {_f(_C, 'l')})",
        _and(
            f"(< {_f(_MID, 'h')} {_f(_A, 'h')})",
            f"(< {_f(_MID, 'h')} {_f(_C, 'h')})",
        ),
    ),
)

# isInclusionNormalized a b c :=
#   ¬ (a.h ≤ b.h ∧ a.l ≥ b.l) ∧ ¬ (b.h ≤ a.h ∧ b.l ≥ a.l) ∧
#   ¬ (c.h ≤ b.h ∧ c.l ≥ b.l) ∧ ¬ (b.h ≤ c.h ∧ b.l ≥ c.l)
# (a = first, b = mid, c = last). ≤ -> <= ; ≥ -> >= ; ¬ -> not.
_INC_BODY = _and(
    _not(_and(f"(<= {_f(_A, 'h')} {_f(_MID, 'h')})", f"(>= {_f(_A, 'l')} {_f(_MID, 'l')})")),
    _and(
        _not(_and(f"(<= {_f(_MID, 'h')} {_f(_A, 'h')})", f"(>= {_f(_MID, 'l')} {_f(_A, 'l')})")),
        _and(
            _not(_and(f"(<= {_f(_C, 'h')} {_f(_MID, 'h')})", f"(>= {_f(_C, 'l')} {_f(_MID, 'l')})")),
            _not(_and(f"(<= {_f(_MID, 'h')} {_f(_C, 'h')})", f"(>= {_f(_MID, 'l')} {_f(_C, 'l')})")),
        ),
    ),
)


def _windowed(bars, body):
    """Map the Def-3 body over every 3-bar window of `bars`."""
    return f"(let (bars {bars}) (map (window bars 3) (w) (let (mid {_MID}) {body})))"


# ---------------------------------------------------------------------------
# 笔 SEPARATION KERNEL (新笔) — the next layer down from 分型 (geometry) to 笔 (stroke).
#
# This encodes a REAL audited bug fix. The 108课-vs-impl audit (proven in
# grounding/chanlun_bi_kline_rule_grounding.py) found the runtime `strokes` program gates two
# opposite fractals on `f.idx − anchor.idx ≥ δmin` with default **δmin=1** — neither 老笔 nor 新笔
# (the audit bug). The MATH VERDICT, exhaustively grounded in that file:
#
#     新笔(t, b)  ⟺  |p_b − p_t| ≥ 4      (顶/底分型 不共用K线 ∧ 极值间 ≥3 K线)
#
# So the faithful 新笔-separation detector, written as a residua-Scheme program (a 2-pivot
# separation predicate, env-parameterized by the two pivot indices pt/pb), is exactly the
# index-difference gate `|p_b − p_t| ≥ 4`. This mirrors chanlun_bi_kline_rule_grounding's
# XINBI_DMIN = 4 boundary CHARACTER-FOR-CHARACTER (the δmin clause), the audited FIX.
#
# HONEST SCOPE: this is the 新笔 SEPARATION KERNEL (the `δmin` clause of the opposite-far branch in
# lean/Chanlun/Stroke.lean#step / StrokeUniqueness.lean#IsValidBi_from), NOT the full list-structural
# `IsValidBi` validity (which is over `List Fractal` — a known discovered residue R4, a list-
# decomposition lock this 2-pivot detector does NOT capture). See chanlun_domain_lock.py.
_BI_SEPARATION = "(>= (abs (- pb pt)) 4)"   # 新笔 ⟺ |p_b − p_t| ≥ 4 (the audited δmin=4 fix)

# Sample env: the exact δ=4 boundary from the grounding proof — pt=0,pb=4 → true (≥4: 新笔);
# pt=0,pb=3 → false (only 3 separation: shared K-lines / <3 between extremes — NOT a 新笔). `abs`
# makes the predicate order-independent (a 底→顶 pair at pt=4,pb=0 is the same 新笔).
_BI_SEPARATION_ENV = {"pt": 0, "pb": 4}


# ---------------------------------------------------------------------------
# 笔-DECOMPOSITION PROGRAM (笔的唯一分解) — R4, the FULL list-structural 笔 validity.
#
# The 新笔 SEPARATION KERNEL above (`bi_separation`) is a 2-pivot predicate — it captures only the
# δmin CLAUSE of the opposite-far branch. It does NOT decide whether a WHOLE `List Stroke` is a valid
# 笔 decomposition of a `List Fractal` (the discovered residue R4, the window-local detector vs
# list-structural validity gap the 分型/separation locks could not reach).
#
# THIS program closes R4. It is the FAITHFUL 笔-decomposition as a residua-Scheme `fold` over a
# `List Fractal`, mirroring `lean/Chanlun/StrokeUniqueness.lean#IsValidBi_from` (≡ the greedy
# `Stroke.step` fold) CHARACTER-FOR-CHARACTER at δmin=4. The fold carries the EXACT Lean state
# `StrokeState = ⟨anchor : Option Fractal, out : List Stroke⟩` (a residua record), and the body is the
# three-branch `step δmin`:
#
#   step δmin ⟨anchor, out⟩ f =
#     | anchor = none           → ⟨some f, out⟩                                   (bootstrap)
#     | some a, a.kind = f.kind → ⟨some (pickRep a f), out⟩                       (same-kind: extremal rep)
#     | some a, f.idx−a.idx ≥ δmin → ⟨some f, ⟨a.idx,f.idx,emitDir f⟩ :: out⟩     (opposite-far: EMIT 笔)
#     | some a, else            → ⟨some a, out⟩                                    (opposite-close: keep)
#
# The output `(field … out)` is the 笔 list. `strokes frs δmin := (foldl step empty).out.reverse`;
# we build `out` with forward `append` (not prepend), so the program's `out` IS `strokes frs 4` in
# final order — i.e. EXACTLY the `alt` that `IsValidBi frs 4 alt` accepts. (`strokes_unique` then
# gives THE unique 笔.) Encodings, mirroring the Lean defs verbatim:
#   • Option Fractal anchor → a record with `present` ∈ {0,1}; `present 0` ≡ `none` (bootstrap branch).
#   • FractalKind  → kind ∈ {1=top, 2=bottom}; `a.kind = f.kind` ≡ `(= (field a kind) (field f kind))`.
#   • pickRep cur cand → top: higher h (`(> f.h a.h)`); bottom: lower l (`(< f.l a.l)`) — Stroke.lean §2.
#   • emitDir target → top→up, bottom→down; the emitted `dir` IS `f.kind` (1=up≡top, 2=down≡bottom).
#   • the δmin gate → `(>= (- (field f idx) (field a idx)) 4)` — the SAME δmin=4 fix as bi_separation,
#     now the opposite-far emit gate of the WHOLE fold (not a 2-pivot predicate).
#
# A produced 笔 list is NOT a proof: the obligation locks to StrokeUniqueness#IsValidBi born
# undischarged; only cc's lake proof `IsValidBi frs 4 (evalL(bi_decomposition frs))` discharges it.
#
# Fixed FRACTAL sample (the ict_residua BARS analog) — an alternating top/bottom 分型 list chosen to
# exercise ALL FOUR branches and stay non-vacuous (records: idx + kind + extremes h/l):
#   f0(idx0,top  h130 l120)  bootstrap         → anchor=f0
#   f1(idx2,top  h140 l125)  same-kind pickRep → 140>130 ⇒ anchor=f1 (extremal top)
#   f2(idx6,bot  h95  l60 )  opposite, 6−2=4≥4 → EMIT ⟨2,6,down⟩, anchor=f2
#   f3(idx8,top  h150 l130)  opposite, 8−6=2<4 → KEEP anchor=f2 (NO emit — the close-gap branch)
#   f4(idx12,top h160 l140)  opposite,12−6=6≥4 → EMIT ⟨6,12,up⟩, anchor=f4
# ⇒ the unique δ=4 决定 decomposition = [⟨2,6,down⟩, ⟨6,12,up⟩] (= strokes frs 4 = the IsValidBi alt).
_BI_FRS = """(append (singleton (record (idx 0)  (kind 1) (h 130) (l 120)))
        (append (singleton (record (idx 2)  (kind 1) (h 140) (l 125)))
        (append (singleton (record (idx 6)  (kind 2) (h 95)  (l 60)))
        (append (singleton (record (idx 8)  (kind 1) (h 150) (l 130)))
                (singleton (record (idx 12) (kind 1) (h 160) (l 140)))))))"""

# `some f` as the anchor record (present=1, carrying the fractal's idx/kind/extremes).
_FREC = ("(record (present 1) (idx (field f idx)) (kind (field f kind)) "
         "(h (field f h)) (l (field f l)))")
# `none` anchor — present=0 (the StrokeState.empty bootstrap; field values are inert placeholders).
_BI_NONE_ANCHOR = "(record (present 0) (idx 0) (kind 0) (h 0) (l 0))"
# the emitted 笔 ⟨a.idx, f.idx, emitDir f⟩ (dir = f.kind: 1=up≡top, 2=down≡bottom).
_BI_EMIT = "(record (from_idx (field a idx)) (to_idx (field f idx)) (dir (field f kind)))"

# The fold BODY = `step δmin` (three branches, with the none-bootstrap as the outermost `if`). `acc`
# is the StrokeState record ⟨anchor, out⟩; `f` is the current Fractal. δmin=4 (the audited fix).
_BI_STEP_BODY = f"""(let (a (field acc anchor))
  (if (= (field a present) 0)
      (record (anchor {_FREC}) (out (field acc out)))
      (if (= (field a kind) (field f kind))
          (record
            (anchor
              (if (= (field a kind) 1)
                  (if (> (field f h) (field a h)) {_FREC} a)
                  (if (< (field f l) (field a l)) {_FREC} a)))
            (out (field acc out)))
          (if (>= (- (field f idx) (field a idx)) 4)
              (record (anchor {_FREC})
                      (out (append (field acc out) (singleton {_BI_EMIT}))))
              acc))))"""

# `strokes frs 4` as a fold: foldl step empty, then project `.out` (built forward ⇒ already in
# final 笔 order). This is the residua-Scheme PROGRAM whose evalL the lock binds to IsValidBi.
_BI_DECOMPOSITION = (f"(field (fold {_BI_FRS} "
                     f"(record (anchor {_BI_NONE_ANCHOR}) (out (empty-list))) "
                     f"(acc f) {_BI_STEP_BODY}) out)")


# name -> (scheme, env). env=None: the window detectors carry their own sample bars inline (the
# residua-Scheme body is the load-bearing artifact; the sample only makes the value non-vacuous).
# bi_separation carries an env {pt, pb}: the 2-pivot 新笔-separation predicate is parameterized by
# the top/bottom pivot indices (the body is the load-bearing artifact; the env picks a sample pair).
# bi_decomposition carries its fractal list inline (env=None) — the fold body is the load-bearing
# artifact (the full IsValidBi state machine); the fixed sample just makes the 笔 list non-vacuous.
PRIMS = {
    # ---- 分型 Def-3 a-gate (= isTopFractal / isBottomFractal) over 3-bar windows ----
    "top_fractal":    (_windowed(BARS, _TOP_BODY), None),
    "bottom_fractal": (_windowed(BARS, _BOTTOM_BODY), None),
    # ---- 包含关系 precondition (= isInclusionNormalized) — the Def-3 upstream gate ----
    "inclusion_normalized": (_windowed(WIN_NORMALIZED, _INC_BODY), None),
    # ---- 笔 新笔 SEPARATION KERNEL (= the δmin clause; 新笔 ⟺ |p_b − p_t| ≥ 4) — the audited fix ----
    "bi_separation": (_BI_SEPARATION, _BI_SEPARATION_ENV),
    # ---- 笔-DECOMPOSITION (= the FULL list-structural IsValidBi validity; R4) — the fold over
    #      `List Fractal` carrying ⟨anchor, out⟩, emitting the unique δ=4 笔 list (= strokes frs 4) ----
    "bi_decomposition": (_BI_DECOMPOSITION, None),
}


def run(scm, env=None):
    """Evaluate a residua-Scheme program (value) + its content-q (proof/dedup key)."""
    v = T.cli("run", "-", stdin=T.program_json(scm, env))
    q = T.cli("q", "-", stdin=T.program_json(scm, env))
    return v.get("val"), q.get("q")


if __name__ == "__main__":
    for name, (scm, env) in PRIMS.items():
        val, q = run(scm, env)
        print(f"{name:22s} val={json.dumps(val):72s} q={q[:16] if q else None}")
