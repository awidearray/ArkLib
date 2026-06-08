#!/usr/bin/env bash
# Kernel axiom-audit harness. Usage: ./audit.sh <relative-lean-file> <fully.qualified.ThmName> [more names...]
# Appends `#print axioms <name>` lines in-file, compiles with `lake env lean`, reports
# axiom dependencies / sorryAx / unknown-constant, then restores the file verbatim.
set -u
F="$1"; shift
BAK="$(mktemp)"
cp "$F" "$BAK"
{
  echo ""
  for n in "$@"; do echo "#print axioms $n"; done
} >> "$F"
OUT="$(timeout 600 lake env lean "$F" 2>&1)"
RC=$?
cp "$BAK" "$F"; rm -f "$BAK"
echo "===== AUDIT $F (rc=$RC) ====="
# Per-theorem axiom verdicts
echo "$OUT" | grep -iE "depends on axioms|sorryAx|propext|Classical|Quot.sound|does not depend|Unknown constant|unknownIdentifier" | sed 's/^/  /'
# Any sorry-uses warnings (which lines)
echo "$OUT" | grep -iE "uses .sorry|declaration uses" | sed 's/^/  WARN: /'
# Any genuine errors
echo "$OUT" | grep -iE "^.*error" | grep -viE "unknownIdentifier|Unknown constant" | head -8 | sed 's/^/  ERR: /'
echo "===== end ====="
