#!/usr/bin/env bash
# CI sorry census: scans ArkLib/ for live `sorry`/`admit` tokens outside
# comments and docstrings.  Exits non-zero if any live holes remain.
#
# Usage:  ./scripts/ci-sorry-census.sh [--json census.json]
#
# The scanner strips Lean line-comments (-- ...) and nested block comments
# (/- ... -/) before looking for `sorry` or `admit` tokens.  Matches inside
# string literals are ignored by the simple heuristic of requiring the token
# to appear as a standalone word boundary match.
#
# Implements requirement (2) of issue #47.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

JSON_OUT=""
for arg in "$@"; do
  case "$arg" in
    --json)  shift; JSON_OUT="$1"; shift ;;
    *)       echo "Unknown arg: $arg" >&2; exit 1 ;;
  esac
done

# ---------------------------------------------------------------------------
# Strip comments from a Lean file and search for sorry/admit tokens.
# Returns lines in the format: filename:line_number:token
# ---------------------------------------------------------------------------
scan_file() {
  local f="$1"
  python3 -c "
import re, sys

path = sys.argv[1]
with open(path, encoding='utf-8', errors='replace') as fh:
    text = fh.read()

# Build per-char comment mask
mask = [False] * len(text)
i, n, depth = 0, len(text), 0
while i < n:
    if depth == 0 and text[i:i+2] == '--':
        j = text.find('\n', i)
        if j == -1: j = n
        for k in range(i, j): mask[k] = True
        i = j
    elif text[i:i+2] == '/-':
        depth += 1
        mask[i] = True
        if i+1 < n: mask[i+1] = True
        i += 2
    elif depth > 0 and text[i:i+2] == '-/':
        depth -= 1
        mask[i] = True
        if i+1 < n: mask[i+1] = True
        i += 2
    else:
        if depth > 0:
            mask[i] = True
        i += 1

# Also mask string literals (simple: single-line \" ... \")
in_string = False
for i, ch in enumerate(text):
    if ch == '\"' and not mask[i]:
        in_string = not in_string
    if in_string:
        mask[i] = True

# Search for sorry/admit as whole-word tokens outside masked regions
token_re = re.compile(r'\b(sorry|admit)\b')
for m in token_re.finditer(text):
    if mask[m.start()]:
        continue
    line_no = text.count('\n', 0, m.start()) + 1
    print(f'{path}:{line_no}:{m.group(1)}')
" "$f"
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
echo "🔍 Running sorry/admit census on ArkLib/ ..."

HOLES=()
while IFS= read -r line; do
  [[ -n "$line" ]] && HOLES+=("$line")
done < <(find ArkLib -name '*.lean' -print0 | sort -z | xargs -0 -I{} bash -c 'scan_file "$@"' _ {} 2>/dev/null || true)

# Also export the scan_file function for xargs
export -f scan_file

# Re-run properly (export doesn't work across subshells in all envs)
HOLES=()
for f in $(find ArkLib -name '*.lean' | sort); do
  while IFS= read -r line; do
    [[ -n "$line" ]] && HOLES+=("$line")
  done < <(scan_file "$f")
done

if [[ -n "$JSON_OUT" ]]; then
  python3 -c "
import json, sys
lines = sys.argv[1:]
entries = []
for l in lines:
    parts = l.split(':', 2)
    if len(parts) == 3:
        entries.append({'file': parts[0], 'line': int(parts[1]), 'token': parts[2]})
json.dump(entries, open('$JSON_OUT', 'w'), indent=2)
print(f'Census written to $JSON_OUT ({len(entries)} entries)')
" "${HOLES[@]+"${HOLES[@]}"}"
fi

COUNT=${#HOLES[@]}

if (( COUNT == 0 )); then
  echo "✅ Sorry census: 0 live holes found."
  exit 0
else
  echo ""
  echo "❌ Sorry census: $COUNT live sorry/admit hole(s) found:"
  echo ""
  for h in "${HOLES[@]}"; do
    echo "  $h"
  done
  echo ""
  echo "All sorry/admit tokens in ArkLib/ must be inside comments or docstrings."
  echo "See issue #47 for details."
  exit 1
fi
