#!/usr/bin/env bash
# Baseline budget analysis for a module
# Usage: ./scripts/baseline_module.sh [--prefix Prefix] [--output file.json] Module.Name [legacy-prefix] [legacy-output]
# Example: ./scripts/baseline_module.sh Budgets.AubinLions.Core

set -euo pipefail

usage() {
  cat <<'EOF' >&2
Usage: baseline_module.sh [options] Module.Name

Options:
  -p, --prefix PREFIX   Override the declaration prefix (default: auto-derived)
  -o, --output FILE     Write JSON to FILE (default: budgets/baseline-<module>-<date>.json)
  -h, --help            Show this message

Legacy positional args [prefix] [output] are still accepted for backwards compatibility.
EOF
}

PREFIX=""
OUTPUT=""
MODULE=""
LEGACY_POSITIONAL=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    -p|--prefix)
      PREFIX="$2"
      shift 2
      ;;
    -o|--output)
      OUTPUT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      while [[ $# -gt 0 ]]; do
        LEGACY_POSITIONAL+=("$1")
        shift
      done
      break
      ;;
    -*)
      echo "Unknown option: $1" >&2
      usage
      exit 1
      ;;
    *)
      if [ -z "$MODULE" ]; then
        MODULE="$1"
      else
        LEGACY_POSITIONAL+=("$1")
      fi
      shift
      ;;
  esac
done

if [ -z "$MODULE" ]; then
  usage
  exit 1
fi

# Legacy positional overrides (prefix/output) for old callers
LEGACY_PREFIX="${LEGACY_POSITIONAL[0]:-}"
LEGACY_OUTPUT="${LEGACY_POSITIONAL[1]:-}"

if [ -z "$PREFIX" ] && [ -n "$LEGACY_PREFIX" ] && [[ "$LEGACY_PREFIX" != -* ]]; then
  PREFIX="$LEGACY_PREFIX"
fi

if [ -z "$OUTPUT" ] && [ -n "$LEGACY_OUTPUT" ] && [[ "$LEGACY_OUTPUT" != -* ]]; then
  OUTPUT="$LEGACY_OUTPUT"
fi

derive_prefix() {
  local module="$1"
  if [[ "$module" == Budgets.* ]]; then
    IFS='.' read -r _ second _rest <<< "$module"
    if [ -n "$second" ]; then
      echo "$second"
      return
    fi
  fi
  if [[ "$module" == *.* ]]; then
    echo "${module##*.}"
  else
    echo "$module"
  fi
}

if [ -z "$PREFIX" ]; then
  PREFIX=$(derive_prefix "$MODULE")
fi

SAFE_MODULE=$(echo "$MODULE" | tr '.' '-' | tr '[:upper:]' '[:lower:]')

if [ -z "$OUTPUT" ]; then
  OUTPUT="budgets/baseline-${SAFE_MODULE}-$(date +%Y%m%d).json"
fi

echo "Baseline analysis: $MODULE" >&2
echo "Using prefix: $PREFIX" >&2
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
    DECL_COUNT=$(grep -c '"decl"' "$OUTPUT" 2>/dev/null || echo "0")
    if [ "$DECL_COUNT" -eq 0 ]; then
      echo "✗ No declarations matched prefix '$PREFIX' in module '$MODULE'" >&2
      echo "  See /tmp/baseline_full.log for details" >&2
      exit 1
    fi

    echo "✓ Analysis complete: $OUTPUT" >&2
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
