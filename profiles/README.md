# Chanlun profiles

Profiles name non-canonical readings without changing `chanlun-v1`.

The canonical semantics are still:

1. `lean/Chanlun/*.lean`
2. `conformance/chanlun-v1/manifest.json`
3. `conformance/chanlun-v1/reference_backend/`

External implementations may be useful for realtime state, plotting, trading
signals, or performance. They enter here as profiles only. A profile is not
canonical unless it proves byte equality against the frozen conformance corpus.

## Rules

- `canonical-v1` is the only trusted geometry profile in this repository.
- External profiles must list every semantic difference they are allowed to
  introduce.
- External profiles must declare whether they contain realtime virtual state.
- A profile may be compared by `differential/compare.py`, but comparison output
  is evidence, not a spec change.
- Changing `conformance/chanlun-v1` is not a profile edit. That requires a new
  corpus version.

