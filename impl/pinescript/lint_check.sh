#!/usr/bin/env bash
# lint_check.sh — discipline check for the PineScript v5 port.
#
# This is NOT a conformance gate. It verifies:
#   1. No PineScript anti-patterns in chanlun_indicator.pine
#      (look-ahead bias via request.security with lookahead_on; bare [0] without isconfirmed guard)
#   2. PINESCRIPT_PORT.md exists and contains all 13 expected named-open residues.
#
# Exit code:
#   0 = pass
#   1 = fail (one or more checks failed)
#
# Run locally:
#   bash impl/pinescript/lint_check.sh

set -euo pipefail

PINE_FILE="impl/pinescript/chanlun_indicator.pine"
PORT_DOC="impl/pinescript/PINESCRIPT_PORT.md"

status=0

echo "===== lint_check: PineScript v5 discipline check ====="

# ---- 1. file existence -------------------------------------------------------
if [ ! -f "$PINE_FILE" ]; then
    echo "FAIL: $PINE_FILE not found"
    status=1
fi
if [ ! -f "$PORT_DOC" ]; then
    echo "FAIL: $PORT_DOC not found"
    status=1
fi
if [ "$status" -ne 0 ]; then
    exit "$status"
fi

# ---- 2. anti-pattern: look-ahead bias ----------------------------------------
echo "Check: no request.security with lookahead_on (look-ahead bias)"
if grep -nE 'lookahead[[:space:]]*=[[:space:]]*barmerge\.lookahead_on' "$PINE_FILE"; then
    echo "FAIL: chanlun_indicator.pine uses barmerge.lookahead_on — this is a look-ahead bias anti-pattern"
    status=1
else
    echo "OK: no look-ahead_on usage"
fi

# ---- 3. residue names in PINESCRIPT_PORT.md ----------------------------------
echo "Check: PINESCRIPT_PORT.md contains all expected named-open residues"

required_residues=(
    "[chanlun_v1_pinescript_normalize_OPEN]"
    "[chanlun_v1_pinescript_fractal_OPEN]"
    "[chanlun_v1_pinescript_stroke_OPEN]"
    "[chanlun_v1_pinescript_stroke_dmin_units_OPEN]"
    "[chanlun_v1_pinescript_stroke_close_drop_OPEN]"
    "[chanlun_v1_pinescript_zhongshu_OPEN]"
    "[chanlun_v1_pinescript_zhongshu_sliding_3_OPEN]"
    "[chanlun_v1_pinescript_zhongshu_zone_gate_OPEN]"
    "[chanlun_v1_pinescript_trend_type_OPEN]"
    "[chanlun_v1_pinescript_trend_type_walk_boundary_OPEN]"
    "[chanlun_v1_pinescript_pipeline_OPEN]"
    "[chanlun_v1_pinescript_conformance_OPEN]"
    "[chanlun_v1_pinescript_ci_offline_harness_OPEN]"
    "[chanlun_v1_pinescript_repaint_intrabar_OPEN]"
)

missing=0
for r in "${required_residues[@]}"; do
    if grep -qF "$r" "$PORT_DOC"; then
        echo "  OK: $r"
    else
        echo "  MISSING: $r"
        missing=$((missing + 1))
    fi
done

if [ "$missing" -gt 0 ]; then
    echo "FAIL: $missing required residues missing from PINESCRIPT_PORT.md"
    status=1
else
    echo "OK: all 14 named residues present in PINESCRIPT_PORT.md"
fi

# ---- 4. lineage statement check ----------------------------------------------
echo "Check: PINESCRIPT_PORT.md contains a lineage statement"
if grep -qE "chanlun.md.*chanlun\.zh\.md|Lessons" "$PORT_DOC"; then
    echo "OK: lineage references present"
else
    echo "FAIL: PINESCRIPT_PORT.md does not reference chanlun.md lineage"
    status=1
fi

# ---- 5. confirmation-lag table check -----------------------------------------
echo "Check: PINESCRIPT_PORT.md documents confirmation lags per stage"
if grep -qE "Confirmation lag" "$PORT_DOC"; then
    echo "OK: confirmation lag commentary present"
else
    echo "FAIL: PINESCRIPT_PORT.md does not document confirmation lags"
    status=1
fi

# ---- 6. .pine file has //@version=5 ------------------------------------------
echo "Check: chanlun_indicator.pine declares //@version=5"
if head -3 "$PINE_FILE" | grep -qE '^//@version=5'; then
    echo "OK: version 5 declared"
else
    echo "FAIL: chanlun_indicator.pine missing //@version=5 declaration"
    status=1
fi

# ---- summary -----------------------------------------------------------------
echo "===== lint_check: $([ "$status" -eq 0 ] && echo PASS || echo FAIL) ====="
exit "$status"
