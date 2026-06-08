#!/usr/bin/env bash
# CI axiom audit: runs `#print axioms` for a pinned list of flagship
# theorems and verifies each depends only on the three blessed axioms:
#   propext, Classical.choice, Quot.sound
#
# Also rejects native_decide, bv_decide, and any custom/non-standard axioms.
#
# Usage:  ./scripts/ci-axiom-audit.sh [--flagship-list path/to/list.txt]
#
# Implements requirements (3) and (4) of issue #47.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

FLAGSHIP_LIST="scripts/flagship-theorems.txt"
for arg in "$@"; do
  case "$arg" in
    --flagship-list)  shift; FLAGSHIP_LIST="$1"; shift ;;
    *)                echo "Unknown arg: $arg" >&2; exit 1 ;;
  esac
done

if [[ ! -f "$FLAGSHIP_LIST" ]]; then
  echo "❌ Flagship theorem list not found: $FLAGSHIP_LIST" >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Blessed axioms — everything else is rejected
# ---------------------------------------------------------------------------
BLESSED_AXIOMS="propext|Classical.choice|Quot.sound"

# ---------------------------------------------------------------------------
# Banned axiom patterns (native_decide, bv_decide, etc.)
# ---------------------------------------------------------------------------
BANNED_PATTERNS="native_decide|bv_decide|sorryAx"

echo "🔎 Running axiom audit against $(wc -l < "$FLAGSHIP_LIST" | tr -d ' ') flagship theorems..."
echo ""

FAILURES=0
SUCCESSES=0
SKIPPED=0

while IFS= read -r entry; do
  # Skip blank lines and comments
  [[ -z "$entry" || "$entry" == \#* ]] && continue

  # Format: MODULE_PATH THEOREM_NAME
  # e.g.: ArkLib/OracleReduction/Composition.lean OracleReduction.compose_completeness
  FILE_PATH="$(echo "$entry" | awk '{print $1}')"
  THEOREM_NAME="$(echo "$entry" | awk '{print $2}')"

  if [[ -z "$FILE_PATH" || -z "$THEOREM_NAME" ]]; then
    echo "⚠️  Skipping malformed entry: $entry"
    SKIPPED=$((SKIPPED + 1))
    continue
  fi

  if [[ ! -f "$FILE_PATH" ]]; then
    echo "❌ FAIL: $THEOREM_NAME — pinned file not found: $FILE_PATH"
    echo "   (update scripts/flagship-theorems.txt if the module moved)"
    FAILURES=$((FAILURES + 1))
    continue
  fi

  # Audit against the built olean: import the module (path → dotted name)
  # and #print axioms in a tiny scratch file. This avoids recompiling the
  # flagship source files (audit.sh appends in-file and re-elaborates the
  # whole file — minutes per multi-thousand-line module; the import-based
  # probe is near-instant after `lake build`).
  MODULE_NAME="$(echo "$FILE_PATH" | sed 's/\.lean$//; s#/#.#g')"
  SCRATCH_BASE="$(mktemp -t axiom-audit-XXXXXX)"
  SCRATCH="$SCRATCH_BASE.lean"
  printf 'import %s\n#print axioms %s\n' "$MODULE_NAME" "$THEOREM_NAME" > "$SCRATCH"
  OUTPUT="$(timeout 600 lake env lean "$SCRATCH" 2>&1)" || true
  rm -f "$SCRATCH" "$SCRATCH_BASE"

  # Check for banned patterns
  if echo "$OUTPUT" | grep -qiE "$BANNED_PATTERNS"; then
    echo "❌ FAIL: $THEOREM_NAME"
    echo "   Banned axiom detected:"
    echo "$OUTPUT" | grep -iE "$BANNED_PATTERNS" | sed 's/^/   /'
    FAILURES=$((FAILURES + 1))
    continue
  fi

  # Check for sorryAx (proof gap)
  if echo "$OUTPUT" | grep -qi "sorryAx"; then
    echo "❌ FAIL: $THEOREM_NAME — uses sorryAx (proof contains sorry)"
    FAILURES=$((FAILURES + 1))
    continue
  fi

  # Unknown constant = pinned theorem no longer exists (rename or deletion).
  # Hard fail: silently skipping would let the gate be laundered by renaming.
  if echo "$OUTPUT" | grep -qiE "Unknown constant|unknownIdentifier"; then
    echo "❌ FAIL: $THEOREM_NAME — unknown identifier (renamed or deleted?)"
    echo "   (update scripts/flagship-theorems.txt if the theorem was renamed)"
    FAILURES=$((FAILURES + 1))
    continue
  fi

  # Extract axiom names from the output
  AXIOM_LINE="$(echo "$OUTPUT" | grep -i 'depends on axioms' || true)"

  if [[ -z "$AXIOM_LINE" ]]; then
    # Check if it doesn't depend on any axioms (which is fine)
    if echo "$OUTPUT" | grep -qi "does not depend on any axioms"; then
      echo "✅ PASS: $THEOREM_NAME (no axioms)"
      SUCCESSES=$((SUCCESSES + 1))
      continue
    fi
    echo "❌ FAIL: $THEOREM_NAME — could not parse axiom output"
    echo "$OUTPUT" | head -10 | sed 's/^/   /'
    FAILURES=$((FAILURES + 1))
    continue
  fi

  # Extract the axiom names after "depends on axioms:"
  AXIOMS_RAW="$(echo "$AXIOM_LINE" | sed 's/.*depends on axioms://' | tr ',' '\n' | sed 's/^[[:space:]]*//' | sed 's/[[:space:]]*$//' | grep -v '^$')"

  BAD_AXIOMS=""
  while IFS= read -r axiom; do
    [[ -z "$axiom" ]] && continue
    # Strip surrounding brackets if present
    axiom="$(echo "$axiom" | tr -d '[]')"
    if ! echo "$axiom" | grep -qE "^($BLESSED_AXIOMS)$"; then
      BAD_AXIOMS="${BAD_AXIOMS:+$BAD_AXIOMS, }$axiom"
    fi
  done <<< "$AXIOMS_RAW"

  if [[ -n "$BAD_AXIOMS" ]]; then
    echo "❌ FAIL: $THEOREM_NAME"
    echo "   Unexpected axiom(s): $BAD_AXIOMS"
    FAILURES=$((FAILURES + 1))
  else
    echo "✅ PASS: $THEOREM_NAME"
    SUCCESSES=$((SUCCESSES + 1))
  fi

done < "$FLAGSHIP_LIST"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Axiom audit results: $SUCCESSES passed, $FAILURES failed, $SKIPPED skipped"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if (( FAILURES > 0 )); then
  echo ""
  echo "❌ Axiom audit failed. All flagship theorems must depend only on:"
  echo "   propext, Classical.choice, Quot.sound"
  echo ""
  echo "Banned: native_decide, bv_decide, sorryAx, and any custom axioms."
  echo "See issue #47 for details."
  exit 1
fi

echo ""
echo "✅ All flagship theorems pass the axiom audit."
exit 0
