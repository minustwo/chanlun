"""Validate the additive profile registry.

This verifier prevents the common footgun: an external implementation is useful,
so it quietly becomes "the spec". Only `canonical-v1` may claim frozen corpus
authority. External profiles must stay declared and label divergence honestly.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "profiles" / "profiles.json"
FROZEN_MANIFEST = ROOT / "conformance" / "chanlun-v1" / "manifest.json"


def _fail(msg: str) -> int:
    print(f"FAIL: {msg}", file=sys.stderr)
    return 1


def main() -> int:
    data = json.loads(REGISTRY.read_text("utf-8"))
    if data.get("schema") != "chanlun-profile-registry-v1":
        return _fail("unexpected registry schema")
    profiles = data.get("profiles")
    if not isinstance(profiles, list) or not profiles:
        return _fail("profiles must be a non-empty list")

    seen = set()
    canonical_id = data.get("canonical_profile")
    canonical_count = 0
    for profile in profiles:
        pid = profile.get("id")
        if not isinstance(pid, str) or not pid:
            return _fail(f"profile has invalid id: {profile!r}")
        if pid in seen:
            return _fail(f"duplicate profile id: {pid}")
        seen.add(pid)

        kind = profile.get("kind")
        proof_kind = profile.get("proof_kind")
        authority = profile.get("authority")
        scope = profile.get("semantic_scope")
        allowed = profile.get("allowed_differences")
        divergence_policy = profile.get("divergence_policy")

        if not isinstance(scope, list) or not all(isinstance(x, str) and x for x in scope):
            return _fail(f"{pid}: semantic_scope must be a non-empty string list")
        if not isinstance(allowed, list):
            return _fail(f"{pid}: allowed_differences must be a list")
        if not isinstance(divergence_policy, str) or not divergence_policy:
            return _fail(f"{pid}: missing divergence_policy")

        if kind == "canonical":
            canonical_count += 1
            if pid != canonical_id:
                return _fail(f"{pid}: canonical kind does not match canonical_profile")
            if authority != "conformance/chanlun-v1/manifest.json":
                return _fail(f"{pid}: canonical authority must be the frozen manifest")
            if proof_kind != "frozen_corpus_identity":
                return _fail(f"{pid}: canonical proof_kind must be frozen_corpus_identity")
            if allowed:
                return _fail(f"{pid}: canonical profile cannot allow semantic differences")
        else:
            if proof_kind == "frozen_corpus_identity" or authority == "conformance/chanlun-v1/manifest.json":
                return _fail(f"{pid}: external profile cannot claim canonical corpus authority")
            if not allowed:
                return _fail(f"{pid}: external profile must document allowed differences")
            if "unknown_divergence" not in divergence_policy:
                return _fail(f"{pid}: external divergence_policy must mention unknown_divergence")

    if canonical_count != 1:
        return _fail(f"expected exactly one canonical profile, found {canonical_count}")
    if not FROZEN_MANIFEST.exists():
        return _fail(f"frozen manifest missing: {FROZEN_MANIFEST}")

    print(f"profiles OK: {len(profiles)} profiles; canonical={canonical_id}; external profiles stay declared")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

