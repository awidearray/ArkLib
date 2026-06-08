#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

remote="${ARKLIB_SYNC_REMOTE:-fork}"
target_branch="${ARKLIB_SYNC_TARGET_BRANCH:-main}"
codex_conflict_timeout="${ARKLIB_SYNC_CODEX_TIMEOUT:-300}"
lock_dir="$repo_dir/.codex/arklib-auto-sync.lock"

if ! mkdir "$lock_dir" 2>/dev/null; then
  printf '[%s] previous sync still running; skipping\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  exit 0
fi
trap 'rmdir "$lock_dir" 2>/dev/null || true' EXIT

stamp="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
printf '[%s] sync start\n' "$stamp"

git config rerere.enabled true
git config pull.rebase false

fix_conflicts_with_codex() {
  local conflict_stamp
  conflict_stamp="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf '[%s] merge conflicts detected; asking Codex to fix them\n' "$conflict_stamp"
  git status --short
  set +e
  timeout "$codex_conflict_timeout" codex exec \
    --cd "$repo_dir" \
    --dangerously-bypass-approvals-and-sandbox \
    "fix all conflicts in this ArkLib repository intelligently. Preserve both sides' useful proof/code changes where possible, do not use blanket ours/theirs resolution, resolve every Git conflict marker, run targeted checks if practical, then leave the merge ready to commit."
  codex_status=$?
  set -e
  if [ "$codex_status" -ne 0 ]; then
    printf '[%s] Codex conflict fixer exited with status %s; checking whether conflicts were still resolved\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$codex_status"
  fi
  if git diff --name-only --diff-filter=U | grep -q .; then
    printf '[%s] Codex returned but unresolved conflicts remain; leaving merge for next cycle\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    git status --short
    exit 1
  fi
}

if [ -d .git/rebase-merge ] || [ -d .git/rebase-apply ]; then
  printf '[%s] rebase in progress; refusing to continue\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  exit 1
fi

if [ -f .git/MERGE_HEAD ]; then
  printf '[%s] merge in progress; checking for conflicts\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  if git diff --name-only --diff-filter=U | grep -q .; then
    fix_conflicts_with_codex
  fi
  git add -A
  git commit --no-edit || true
fi

git add -A
if ! git diff --cached --quiet; then
  git commit -m "auto-sync: save ArkLib work ${stamp}"
else
  printf '[%s] no local changes to commit\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
fi

git fetch "$remote" "$target_branch"

if ! git merge --no-edit "$remote/$target_branch"; then
  fix_conflicts_with_codex
  git add -A
  git commit --no-edit || git commit -m "auto-sync: merge ${remote}/${target_branch} ${stamp}"
fi

git add -A
if ! git diff --cached --quiet; then
  git commit -m "auto-sync: post-merge cleanup ${stamp}"
fi

for push_attempt in 1 2 3; do
  if git push "$remote" "HEAD:${target_branch}"; then
    printf '[%s] sync pushed HEAD to %s/%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$remote" "$target_branch"
    exit 0
  fi
  printf '[%s] push attempt %s failed; fetching and merging latest %s/%s before retry\n' \
    "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$push_attempt" "$remote" "$target_branch"
  git fetch "$remote" "$target_branch"
  if ! git merge --no-edit "$remote/$target_branch"; then
    fix_conflicts_with_codex
    git add -A
    git commit --no-edit || git commit -m "auto-sync: merge ${remote}/${target_branch} after push race ${stamp}"
  fi
  git add -A
  if ! git diff --cached --quiet; then
    git commit -m "auto-sync: post-push-race cleanup ${stamp}"
  fi
done

printf '[%s] failed to push after retries\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
exit 1
