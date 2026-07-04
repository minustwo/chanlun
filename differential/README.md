# Differential comparison

`compare.py` checks candidate backends against the frozen `chanlun-v1` corpus.
It is the gate between external engineering features and canonical geometry.

Supported built-in backends:

- `canonical`: re-runs the in-repo reference backend.
- `fixture-replay`: returns each fixture's expected output. This is a protocol
  sanity check, not an implementation.
- `trade-signal`: calls a real `wepoets1107/chanlun-trade-signal` checkout when
  `CHANLUN_TRADE_SIGNAL_ROOT` is set, or when
  `/tmp/chanlun-externals/chanlun-trade-signal` exists.
- `chanpy`: calls a local `Vespa314/chan.py` checkout through an in-memory
  custom DataAPI when `CHANPY_ROOT` is set, or when
  `/tmp/chanlun-externals/chan.py` exists.
- `czsc-native`: calls `czsc._native` from a GitHub-master-style `czsc`
  install. It deliberately does not fall back to older PyPI Python semantics.
- `czsc-pypi-rs`: calls the PyPI `rs_czsc` runtime from an optional isolated
  venv and exposes only full-pipeline profile comparison.

External backends are intentionally not guessed. Add a backend only when it can
emit one of the corpus stage output shapes exactly. Missing external tools must
be reported as SKIP-LOUD, never PASS.

Result classes:

- `equal`: backend output SHA matches the frozen expected SHA.
- `known_profile_divergence`: a profile declares and witnesses a difference.
- `unknown_divergence`: backend differs without an approved profile explanation.

## Reports

```bash
python3 differential/fetch_external_sources.py chanpy
python3 differential/absorption_report.py
python3 differential/pipeline_projection_report.py
python3 differential/optional_backend_availability.py
python3 differential/source_audit.py
```

To record an explicit online Cargo fetch attempt for `czsc-core`, run:

```bash
python3 differential/optional_backend_availability.py --probe-czsc-core-online
```

To record an explicit PyPI wheel download attempt for the `czsc 0.10.x`
release profile, run:

```bash
python3 differential/optional_backend_availability.py --probe-czsc-pypi-download
```

To build the isolated PyPI release-profile venv under `/tmp`, run:

```bash
python3 differential/install_czsc_pypi_profile.py
```

The installer uses `--no-deps` and reports SKIP-LOUD when import-time runtime
deps such as `pandas` / `pyarrow` are absent. That keeps product-layer
dependencies from being silently treated as geometry evidence.
For runtime probing of the `rs_czsc` geometry package with system-provided
`pandas` / `pyarrow`, run:

```bash
python3 differential/install_czsc_pypi_profile.py --system-site-packages --rs-only
python3 differential/compare.py --backend czsc-pypi-rs --stage pipeline
python3 differential/pipeline_projection_report.py
```

Optional Rust probe for the published `czsc-core` crate:

```bash
cargo run --quiet --manifest-path differential/czsc_core_probe/Cargo.toml -- conformance/chanlun-v1 \
  > /tmp/chanlun-externals/czsc-core-projection.json
python3 differential/pipeline_projection_report.py \
  --czsc-core-json /tmp/chanlun-externals/czsc-core-projection.json
```

- `ABSORPTION_REPORT.md` records runtime differential evidence and SKIP-LOUD
  gaps for optional external backends.
- `PIPELINE_PROJECTION_REPORT.md` compares external full-pipeline object graphs
  against selected canonical fields.
- `OPTIONAL_BACKENDS_REPORT.md` records which optional runtime backends can run
  in the current environment and which ones remain SKIP-LOUD.
- `SOURCE_AUDIT_REPORT.md` records source-level anchors for `chan.py` and
  `czsc`. It is deliberately weaker than runtime equality.
- `fetch_external_sources.py chanpy` fetches the minimal Python source tree
  needed to run `Vespa314/chan.py` under `/tmp/chanlun-externals/chan.py`.

`czsc-native` expects a GitHub-master-style install that exposes
`czsc._native`, produced by the upstream maturin/Cargo build. PyPI `czsc`
0.10.x is an older Python API line and must not be used as evidence for this
backend.
`czsc-core` is also exposed as an optional Rust probe pinned to crate
`czsc-core = 1.0.0-rc.8`; it is not part of default CI because first compile
requires the upstream Rust dependency graph.
PyPI `czsc==0.10.12` is tracked as a separate release profile because it
depends on `rs_czsc` and may differ from GitHub master `_native`.
`czsc-pypi-rs` is currently a profile-local runtime projection: monotonic
empty-BI fixtures have equal projected fields, while nontrivial walk fixtures
diverge because `rs_czsc.CZSC` exposes online analyzer state (`bars_ubi`,
`fx_list`, `ubi_fxs`, `bi_list`) rather than the frozen canonical wire.

Runtime equality is the only path to canonical status. Source audit is useful
for planning adapter work, not for changing `chanlun-v1`.
