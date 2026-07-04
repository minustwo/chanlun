"""Optional external backend adapters for differential comparison.

These adapters call real external source trees when available. They are not
canonical and they do not run in CI unless a caller provides the source path.
Missing source is SKIP-LOUD.
"""
from __future__ import annotations

import contextlib
import datetime as _dt
import importlib
import json
import os
import subprocess
import sys
import types
from pathlib import Path
from typing import Callable


class ExternalBackendSkip(RuntimeError):
    """The backend is not available in this environment."""


class ProfileGap(RuntimeError):
    """The backend cannot emit this corpus stage's canonical wire shape."""


@contextlib.contextmanager
def _prepend_sys_path(path: Path):
    old = list(sys.path)
    sys.path.insert(0, str(path))
    try:
        yield
    finally:
        sys.path[:] = old


def _intish(value):
    if isinstance(value, int):
        return value
    if isinstance(value, float) and value.is_integer():
        return int(value)
    return value


def _trade_signal_root() -> Path:
    raw = os.environ.get("CHANLUN_TRADE_SIGNAL_ROOT") or "/tmp/chanlun-externals/chanlun-trade-signal"
    root = Path(raw)
    if not (root / "app" / "chanlun").exists():
        raise ExternalBackendSkip(
            "SKIP-LOUD: chanlun-trade-signal source not found; set CHANLUN_TRADE_SIGNAL_ROOT"
        )
    return root


def _chanpy_root() -> Path:
    raw = os.environ.get("CHANPY_ROOT") or "/tmp/chanlun-externals/chan.py"
    root = Path(raw)
    if not (root / "Chan.py").exists():
        raise ExternalBackendSkip("SKIP-LOUD: chan.py source not found; set CHANPY_ROOT")
    return root


def _trade_signal_imports():
    root = _trade_signal_root()
    with _prepend_sys_path(root):
        okx = importlib.import_module("app.market.okx")
        kline = importlib.import_module("app.chanlun.kline")
        fractal = importlib.import_module("app.chanlun.fractal")
        stroke = importlib.import_module("app.chanlun.stroke")
        center = importlib.import_module("app.chanlun.center")
        models = importlib.import_module("app.chanlun.models")
    return okx, kline, fractal, stroke, center, models


def _import_optional_module(name: str, source_hint: str):
    try:
        return importlib.import_module(name)
    except Exception as exc:
        raise ExternalBackendSkip(f"SKIP-LOUD: {source_hint} is not importable: {exc}") from exc


def _czsc_native():
    return _import_optional_module("czsc._native", "czsc._native")


def _czsc_pypi_rs_python() -> Path:
    explicit = os.environ.get("CZSC_PYPI_RS_PYTHON")
    if explicit:
        path = Path(explicit)
        if path.exists():
            return path
        raise ExternalBackendSkip(f"SKIP-LOUD: CZSC_PYPI_RS_PYTHON not found: {path}")
    candidates = [
        Path("/tmp/chanlun-externals/czsc-pypi-system-venv/bin/python"),
        Path("/tmp/chanlun-externals/czsc-pypi-venv/bin/python"),
    ]
    for path in candidates:
        if path.exists():
            return path
    raise ExternalBackendSkip(
        "SKIP-LOUD: rs_czsc PyPI venv not found; run install_czsc_pypi_profile.py"
    )


def _run_czsc_pypi_rs_projection(inp: dict) -> dict:
    python = _czsc_pypi_rs_python()
    script = r"""
import datetime as dt
import json
import sys

import rs_czsc


def intish(value):
    if isinstance(value, int):
        return value
    if isinstance(value, float) and value.is_integer():
        return int(value)
    return value


def raw_bars(bars):
    out = []
    for i, bar in enumerate(bars):
        high = float(bar["h"])
        low = float(bar["l"])
        mid = (high + low) / 2.0
        out.append(rs_czsc.RawBar(
            "CHANLUN",
            dt.datetime(2020, 1, 1) + dt.timedelta(days=i),
            rs_czsc.Freq.D,
            mid,
            mid,
            high,
            low,
            1.0,
            1.0,
            i,
        ))
    return out


def fx_kind(mark):
    if mark == rs_czsc.Mark.G:
        return "top"
    if mark == rs_czsc.Mark.D:
        return "bottom"
    raise ValueError(f"unknown mark: {mark!r}")


def bi_dir(direction):
    if direction == rs_czsc.Direction.Up:
        return "up"
    if direction == rs_czsc.Direction.Down:
        return "down"
    raise ValueError(f"unknown direction: {direction!r}")


def raw_ids(fx):
    ids = []
    for new_bar in fx.elements:
        for raw in new_bar.raw_bars:
            ids.append(raw.id)
    return ids


def fx_idx(fx):
    ids = raw_ids(fx)
    return ids[len(ids) // 2] if ids else None


def project(inp):
    bars = inp["bars"]
    if not bars:
        return {"normalized_bars": [], "fractals": [], "strokes": [], "zhongshu_centers": []}
    analyzer = rs_czsc.CZSC(raw_bars(bars), 200)
    fxs = list(analyzer.fx_list) + list(analyzer.ubi_fxs)
    return {
        "normalized_bars": [
            {"l": intish(bar.low), "h": intish(bar.high)}
            for bar in analyzer.bars_ubi
        ],
        "fractals": [
            {"idx": fx_idx(fx), "kind": fx_kind(fx.mark), "h": intish(fx.high), "l": intish(fx.low)}
            for fx in fxs
        ],
        "strokes": [
            {
                "from_idx": fx_idx(bi.fx_a),
                "to_idx": fx_idx(bi.fx_b),
                "dir": bi_dir(bi.direction),
                "from_p": intish(bi.fx_a.fx),
                "to_p": intish(bi.fx_b.fx),
            }
            for bi in analyzer.bi_list
        ],
        "zhongshu_centers": [],
    }


print(json.dumps(project(json.load(sys.stdin)), sort_keys=True, separators=(",", ":")))
"""
    proc = subprocess.run(
        [str(python), "-c", script],
        input=json.dumps(inp, sort_keys=True),
        cwd=Path(__file__).resolve().parents[1],
        text=True,
        capture_output=True,
        timeout=30,
    )
    if proc.returncode != 0:
        reason = (proc.stderr or proc.stdout).strip().splitlines()
        note = reason[-1] if reason else f"exit {proc.returncode}"
        raise ExternalBackendSkip(f"SKIP-LOUD: rs_czsc PyPI projection failed: {note}")
    return json.loads(proc.stdout)


def _bars_to_czsc_raw(bars):
    native = _czsc_native()
    freq = native.Freq("D")
    raw = []
    for i, bar in enumerate(bars):
        h = float(bar["h"])
        l = float(bar["l"])
        mid = (h + l) / 2.0
        raw.append(native.RawBar(
            "CHANLUN",
            _dt.datetime(2020, 1, 1) + _dt.timedelta(days=i),
            freq,
            mid,
            mid,
            h,
            l,
            1.0,
            1.0,
            i,
        ))
    return raw


def _czsc_analyzer(bars, *, min_bi_len: int = 6):
    native = _czsc_native()
    raw = _bars_to_czsc_raw(bars)
    if not raw:
        raise ProfileGap("czsc._native CZSC requires at least one RawBar")
    return native.CZSC(raw, 200, min_bi_len)


def _czsc_mark_name(mark) -> str:
    name = getattr(mark, "name", None) or str(mark)
    if name in ("G", "顶分型", "Mark.G"):
        return "top"
    if name in ("D", "底分型", "Mark.D"):
        return "bottom"
    raise ProfileGap(f"czsc._native emitted unknown fractal mark {mark!r}")


def _czsc_dir_name(direction) -> str:
    name = getattr(direction, "name", None) or str(direction)
    if name in ("Up", "向上", "Direction.Up"):
        return "up"
    if name in ("Down", "向下", "Direction.Down"):
        return "down"
    raise ProfileGap(f"czsc._native emitted unknown BI direction {direction!r}")


def _czsc_float_to_wire(value):
    if isinstance(value, int):
        return value
    if isinstance(value, float) and value.is_integer():
        return int(value)
    return value


def _bars_to_candles(bars):
    okx, *_ = _trade_signal_imports()
    out = []
    for i, bar in enumerate(bars):
        h = float(bar["h"])
        l = float(bar["l"])
        mid = (h + l) / 2.0
        out.append(okx.OKXCandle(
            ts=1_700_000_000_000 + i * 60_000,
            open=mid,
            high=h,
            low=l,
            close=mid,
            volume=1.0,
            confirmed=True,
        ))
    return out


def _install_chanpy_fixture_api(bars):
    """Register an in-memory chan.py DataAPI module for fixture bars."""
    cenum = importlib.import_module("Common.CEnum")
    ctime = importlib.import_module("Common.CTime")
    klu = importlib.import_module("KLine.KLine_Unit")

    class CFixtureAPI:
        def __init__(self, code, k_type, begin_date, end_date, autype):
            self.code = code
            self.k_type = k_type

        def get_kl_data(self):
            start = _dt.date(2020, 1, 1)
            for i, bar in enumerate(bars):
                h = float(bar["h"])
                l = float(bar["l"])
                mid = (h + l) / 2.0
                day = start + _dt.timedelta(days=i)
                yield klu.CKLine_Unit({
                    cenum.DATA_FIELD.FIELD_TIME: ctime.CTime(day.year, day.month, day.day, 0, 0),
                    cenum.DATA_FIELD.FIELD_OPEN: mid,
                    cenum.DATA_FIELD.FIELD_HIGH: h,
                    cenum.DATA_FIELD.FIELD_LOW: l,
                    cenum.DATA_FIELD.FIELD_CLOSE: mid,
                })

        @classmethod
        def do_init(cls):
            return None

        @classmethod
        def do_close(cls):
            return None

    module = types.ModuleType("DataAPI.chanlun_fixture")
    module.CFixtureAPI = CFixtureAPI
    sys.modules["DataAPI.chanlun_fixture"] = module


def _chanpy_analyzer(bars):
    root = _chanpy_root()
    with _prepend_sys_path(root):
        _install_chanpy_fixture_api(bars)
        chan_mod = importlib.import_module("Chan")
        config_mod = importlib.import_module("ChanConfig")
        cenum = importlib.import_module("Common.CEnum")
        config = config_mod.CChanConfig({
            "kl_data_check": False,
            "print_warning": False,
            "print_err_time": False,
            "zs_combine": False,
        })
        return chan_mod.CChan(
            "CHANLUN",
            data_src="custom:chanlun_fixture.CFixtureAPI",
            lv_list=[cenum.KL_TYPE.K_DAY],
            config=config,
        )


def _chanpy_fx_kind(fx, cenum):
    if fx == cenum.FX_TYPE.TOP:
        return "top"
    if fx == cenum.FX_TYPE.BOTTOM:
        return "bottom"
    return None


def _chanpy_dir(direction, cenum):
    if direction == cenum.BI_DIR.UP:
        return "up"
    if direction == cenum.BI_DIR.DOWN:
        return "down"
    raise ProfileGap(f"chan.py emitted unknown BI direction {direction!r}")


def chanpy_pipeline_projection(inp: dict) -> dict:
    """Project chan.py's own pipeline objects into comparable wire fragments."""
    bars = inp["bars"]
    if not bars:
        return {"normalized_bars": [], "fractals": [], "strokes": [], "zhongshu_centers": []}
    chan = _chanpy_analyzer(bars)
    cenum = importlib.import_module("Common.CEnum")
    kl = chan[0]
    normalized = [{"l": _intish(klc.low), "h": _intish(klc.high)} for klc in kl.lst]
    fractals = []
    for klc in kl.lst:
        kind = _chanpy_fx_kind(klc.fx, cenum)
        if kind is not None:
            fractals.append({"idx": klc.idx, "kind": kind, "h": _intish(klc.high), "l": _intish(klc.low)})
    strokes = []
    for bi in kl.bi_list:
        strokes.append({
            "from_idx": bi.begin_klc.idx,
            "to_idx": bi.end_klc.idx,
            "dir": _chanpy_dir(bi.dir, cenum),
            "from_p": _intish(bi.get_begin_val()),
            "to_p": _intish(bi.get_end_val()),
        })
    centers = []
    for zs in kl.zs_list:
        centers.append({
            "start": zs.begin_bi.idx,
            "end": zs.end_bi.idx,
            "ZD": _intish(zs.low),
            "ZG": _intish(zs.high),
            "n": zs.end_bi.idx - zs.begin_bi.idx + 1,
        })
    return {
        "normalized_bars": normalized,
        "fractals": fractals,
        "strokes": strokes,
        "zhongshu_centers": centers,
    }


def czsc_pypi_rs_projection(inp: dict) -> dict:
    """Project PyPI rs_czsc's runtime object graph into comparable fragments."""
    return _run_czsc_pypi_rs_projection(inp)


def backend_trade_signal(stage: str, inp, fixture: dict):
    """Run wepoets1107/chanlun-trade-signal where its semantics has a stage.

    This is a profile comparison, not a conformance claim. Some stage outputs
    cannot match the canonical wire exactly because the workbench does not carry
    all canonical witnesses, for example stroke dispositions.
    """
    _okx, kline, fractal, stroke, center, models = _trade_signal_imports()

    if stage == "normalize":
        normalized = kline.normalize_candles(_bars_to_candles(inp))
        return [{"l": _intish(x.low), "h": _intish(x.high)} for x in normalized]

    if stage == "fractal":
        candles = _bars_to_candles(inp)
        # min_effective_bars=1 keeps the closest shape to Def-3; the workbench
        # still performs adjacent same-kind dedupe, so divergence remains
        # profile-local evidence.
        frs = fractal.detect_fractals(candles, min_effective_bars=1)
        out = []
        for f in frs:
            if f.index < 0 or f.index >= len(inp):
                continue
            b = inp[f.index]
            out.append({"idx": f.index, "kind": f.kind, "h": b["h"], "l": b["l"]})
        return out

    if stage == "stroke":
        frs = []
        for f in inp["fractals"]:
            price = f["h"] if f["kind"] == "top" else f["l"]
            frs.append(models.Fractal(index=f["idx"], ts=1_700_000_000_000 + f["idx"] * 60_000,
                                      kind=f["kind"], price=float(price)))
        sts = stroke.build_strokes(frs, min_stroke_bars=inp["dmin"])
        out = []
        for s in sts:
            out.append({
                "from_idx": s.start_index,
                "to_idx": s.end_index,
                "dir": s.direction,
                "from_p": _intish(s.start_price),
                "to_p": _intish(s.end_price),
            })
        raise ProfileGap({
            "reason": "chanlun-trade-signal does not expose canonical stroke dispositions",
            "partial": {"strokes": out},
        })

    if stage == "zhongshu":
        sts = []
        for pos, el in enumerate(inp["elements"]):
            direction = "up" if pos % 2 else "down"
            sts.append(models.Stroke(
                start_index=pos,
                end_index=pos,
                direction=direction,
                start_price=float(el["lo"]),
                end_price=float(el["hi"]),
                high=float(el["hi"]),
                low=float(el["lo"]),
            ))
        centers = center.build_centers(sts)
        return [
            {"start": c.start_index, "end": c.end_index, "ZD": _intish(c.low), "ZG": _intish(c.high), "n": c.stroke_count}
            for c in centers
        ]

    raise ProfileGap(f"chanlun-trade-signal has no canonical output for stage {stage!r}")


def backend_chanpy(stage: str, inp, fixture: dict):
    """Run Vespa314/chan.py on fixture bars when its source tree is available."""
    _chanpy_root()
    if stage == "normalize":
        if not inp:
            return []
        chan = _chanpy_analyzer(inp)
        kline_list = chan[0]
        return [{"l": _intish(klc.low), "h": _intish(klc.high)} for klc in kline_list.lst]

    if stage == "fractal":
        chan = _chanpy_analyzer(inp)
        cenum = importlib.import_module("Common.CEnum")
        out = []
        for klc in chan[0].lst:
            kind = _chanpy_fx_kind(klc.fx, cenum)
            if kind is None:
                continue
            out.append({"idx": klc.idx, "kind": kind, "h": _intish(klc.high), "l": _intish(klc.low)})
        return out

    if stage == "stroke":
        bars = fixture.get("pipeline_input")
        if bars is None:
            raise ProfileGap("chan.py BI comparison needs raw bars; corpus stroke fixtures contain fractals")
        chan = _chanpy_analyzer(bars)
        cenum = importlib.import_module("Common.CEnum")
        out = []
        for bi in chan[0].bi_list:
            out.append({
                "from_idx": bi.begin_klc.idx,
                "to_idx": bi.end_klc.idx,
                "dir": _chanpy_dir(bi.dir, cenum),
                "from_p": _intish(bi.get_begin_val()),
                "to_p": _intish(bi.get_end_val()),
            })
        raise ProfileGap({
            "reason": "chan.py BI is computed from its own KLine state and does not expose canonical dispositions",
            "partial": {"strokes": out},
        })

    if stage == "zhongshu":
        raise ProfileGap("chan.py ZS requires chan.py BI/Seg objects; corpus zhongshu fixtures contain canonical elements")

    raise ProfileGap(f"chan.py has no canonical output for stage {stage!r}")


def backend_czsc_native(stage: str, inp, fixture: dict):
    """Run waditu/czsc's Rust/PyO3 native analyzer when installed.

    The current GitHub master exposes `czsc._native` as the geometry core. This
    adapter intentionally does not install it; callers must provide an
    environment where the same package is importable. PyPI may lag the GitHub
    master API, so missing `_native` is a SKIP-LOUD rather than a fallback to an
    older Python implementation.
    """
    native = _czsc_native()

    if stage == "normalize":
        analyzer = _czsc_analyzer(inp)
        bars_ubi = getattr(analyzer, "bars_ubi", None)
        if bars_ubi is None:
            raise ProfileGap("czsc._native CZSC does not expose bars_ubi")
        return [
            {"l": _czsc_float_to_wire(x.low), "h": _czsc_float_to_wire(x.high)}
            for x in bars_ubi
        ]

    if stage == "fractal":
        analyzer = _czsc_analyzer(inp)
        if hasattr(analyzer, "get_fx_list"):
            fxs = analyzer.get_fx_list()
        else:
            fxs = native.check_fxs(getattr(analyzer, "bars_ubi", []))
        out = []
        for fx in fxs:
            raw_bars = getattr(fx, "raw_bars", None) or []
            if not raw_bars:
                raise ProfileGap("czsc._native FX does not expose raw_bars")
            idx = raw_bars[len(raw_bars) // 2].id
            b = inp[idx]
            out.append({"idx": idx, "kind": _czsc_mark_name(fx.mark), "h": b["h"], "l": b["l"]})
        return out

    if stage == "stroke":
        # Feed bars, not precomputed fractals, because czsc._native BI carries
        # richer NewBar/FX state than the corpus stage input. This comparison is
        # intentionally a profile comparison, not canonical conformance.
        bars = fixture.get("pipeline_input")
        if bars is None:
            raise ProfileGap("czsc._native stroke comparison needs raw bars; corpus stroke fixtures contain fractals")
        analyzer = _czsc_analyzer(bars, min_bi_len=inp.get("dmin", 6) if isinstance(inp, dict) else 6)
        out = []
        for bi in getattr(analyzer, "bi_list", []):
            fx_a = bi.fx_a
            fx_b = bi.fx_b
            a_raw = fx_a.raw_bars[len(fx_a.raw_bars) // 2]
            b_raw = fx_b.raw_bars[len(fx_b.raw_bars) // 2]
            out.append({
                "from_idx": a_raw.id,
                "to_idx": b_raw.id,
                "dir": _czsc_dir_name(bi.direction),
                "from_p": _czsc_float_to_wire(fx_a.fx),
                "to_p": _czsc_float_to_wire(fx_b.fx),
            })
        raise ProfileGap({
            "reason": "czsc._native BI does not expose canonical stroke dispositions from corpus fractal input",
            "partial": {"strokes": out},
        })

    if stage == "zhongshu":
        raise ProfileGap("czsc._native ZS requires BI objects; corpus zhongshu fixtures contain canonical elements")

    raise ProfileGap(f"czsc._native has no canonical output for stage {stage!r}")


def backend_czsc_pypi_rs(stage: str, inp, fixture: dict):
    """Run PyPI rs_czsc through its runtime analyzer for pipeline fixtures."""
    if stage == "pipeline":
        return czsc_pypi_rs_projection(inp)
    raise ProfileGap(
        "rs_czsc PyPI runtime comparison is exposed as full-pipeline projection only"
    )


EXTERNAL_BACKENDS: dict[str, Callable] = {
    "trade-signal": backend_trade_signal,
    "chanpy": backend_chanpy,
    "czsc-native": backend_czsc_native,
    "czsc-pypi-rs": backend_czsc_pypi_rs,
}
