#!/usr/bin/env bash
# Baseline budget analysis for a module
# Usage: ./scripts/baseline_module.sh <Module.To.Import> <Prefix.To.Analyze> [output.json]
# Example: ./scripts/baseline_module.sh Batteries.Data.List.Basic List budgets/baseline-list.json

set -euo pipefail

MODULE="${1:-}"
PREFIX="${2:-$MODULE}"
OUTPUT="${3:-budgets/baseline-$(echo "$PREFIX" | tr '.' '-' | tr '[:upper:]' '[:lower:]')-$(date +%Y%m%d).json}"

if [ -z "$MODULE" ]; then
  echo "Usage: $0 <Module.To.Import> [Prefix.To.Analyze] [output.json]" >&2
  echo "Example: $0 Batteries.Data.List.Basic List" >&2
  echo "         (imports Batteries.Data.List.Basic, analyzes all List.* declarations)" >&2
  exit 1
fi

echo "Baseline analysis: $MODULE" >&2
echo "Output: $OUTPUT" >&2
echo "" >&2

# Create temporary Lean file in tests directory
TMP_FILE="tests/BaselineTemp_$(date +%s).lean"
trap "rm -f $TMP_FILE" EXIT

cat > "$TMP_FILE" << EOF
-- Auto-generated baseline analysis
-- Import: $MODULE
-- Analyze prefix: $PREFIX
-- Filter by module: $MODULE
import $MODULE
import WBudget.Baseline

-- Run baseline analysis on all declarations with prefix $PREFIX from module $MODULE
#baseline_module $PREFIX $MODULE
EOF

echo "Running analysis (this may take a while)..." >&2

# Run lean with lake environment to get proper dependencies
# Capture stderr (where info messages go) and extract JSON
# Filter for JSON content: [, {, }, ], and object content lines
if lake env lean "$TMP_FILE" 2>&1 | tee /tmp/baseline_full.log | grep -E '^\[|^\{|^\}|^\]|^  "' > "$OUTPUT"; then
  # Check if we got valid JSON output
  if grep -q '\[' "$OUTPUT" 2>/dev/null; then
    echo "✓ Analysis complete: $OUTPUT" >&2

    # Show summary
    DECL_COUNT=$(grep -c '"decl"' "$OUTPUT" 2>/dev/null || echo "0")
    echo "  Analyzed $DECL_COUNT declarations" >&2
  else
    echo "✗ No JSON output found - see /tmp/baseline_full.log" >&2
    cat /tmp/baseline_full.log >&2
    exit 1
  fi
else
  echo "✗ Analysis failed - see /tmp/baseline_full.log" >&2
  cat /tmp/baseline_full.log >&2
  exit 1
fi
