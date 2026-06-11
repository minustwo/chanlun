"""Reference backend for the `chanlun-v1` conformance corpus.

Each submodule is a self-contained pure-stdlib oracle, copied from `grounding/*.py`
in this repo and standalone in `fractal.py`. The Lean side proves each ≡ its
README/chanlun.md definition. The corpus FREEZES (input → expected-output) bytes
over this backend; Phase-3 multi-language implementations conform by reproducing
the SHA-256 of every fixture's canonical output.

Lineage:

    Lean MWE (lean/Chanlun/*.lean)
        ≡
    Python grounding (grounding/chanlun_*_grounding.py)
        ≡
    Reference backend (conformance/chanlun-v1/reference_backend/*.py)
        ⇒  fixtures (conformance/chanlun-v1/fixtures/*.json)
        ⇒  manifest (conformance/chanlun-v1/manifest.json)
"""
