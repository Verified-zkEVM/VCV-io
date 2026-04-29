#!/usr/bin/env bash
# Build a fully anonymized snapshot of `main` and force-push it as
# `ccs26-submission`, suitable for double-blind review through
# https://anonymous.4open.science/.
#
# Usage:
#   scripts/anonymize-for-submission.sh                  # main -> origin/ccs26-submission
#   scripts/anonymize-for-submission.sh --dry-run        # build snapshot, skip push, keep worktree
#   scripts/anonymize-for-submission.sh [--dry-run] <src> <branch> <remote>
#
# Re-run any time `main` advances. The target branch is recreated as a
# single orphan commit, so git history is also anonymized.
#
# This script lives only on the `ccs26-submission` branch (it is not
# present on `main`) and self-preserves: every run copies its current
# contents into the new orphan commit, so subsequent runs always find
# it on `ccs26-submission`.
#
# Run it from anywhere inside a clone of the VCV-io repository. It
# does not modify the current worktree; all work happens in a
# throwaway worktree under $TMPDIR.

set -euo pipefail

# Resolve the absolute path of this script before any cd, so we can
# copy the live version into the orphan commit further down.
SCRIPT_PATH="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)/$(basename "$0")"

DRY_RUN=0
if [[ "${1:-}" == "--dry-run" ]]; then
  DRY_RUN=1
  shift
fi

SOURCE_REF="${1:-origin/main}"
TARGET_BRANCH="${2:-ccs26-submission}"
REMOTE="${3:-origin}"

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

# Resolve a fetchable ref name from $SOURCE_REF (e.g. origin/main -> main).
SOURCE_REF_NAME="${SOURCE_REF#${REMOTE}/}"

echo "==> Fetching $REMOTE/$SOURCE_REF_NAME and $TARGET_BRANCH"
git fetch "$REMOTE" "$SOURCE_REF_NAME"
git fetch "$REMOTE" "$TARGET_BRANCH" || true

TMP_WT="$(mktemp -d -t vcvio-anon.XXXXXX)"
TMP_BRANCH="anon-$(date +%s)-$$"

cleanup() {
  cd "$REPO_ROOT"
  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "==> Dry run: leaving worktree in place at $TMP_WT"
    echo "    Inspect with: ( cd $TMP_WT && git log -1 && git ls-files | head )"
    echo "    Remove with:  git worktree remove --force $TMP_WT && git branch -D $TMP_BRANCH"
    return
  fi
  git worktree remove --force "$TMP_WT" >/dev/null 2>&1 || true
  git branch -D "$TMP_BRANCH" >/dev/null 2>&1 || true
  rm -rf "$TMP_WT"
  git worktree prune >/dev/null 2>&1 || true
}
trap cleanup EXIT

echo "==> Creating temporary worktree at $TMP_WT (orphan branch $TMP_BRANCH)"
git worktree add --detach "$TMP_WT" "$SOURCE_REF" >/dev/null
cd "$TMP_WT"
git checkout --orphan "$TMP_BRANCH"

echo "==> Removing identifying top-level files and directories"
rm -rf \
  AGENTS.md \
  CLAUDE.md \
  CONTRIBUTING.md \
  .github \
  .ignore \
  docs/agents

ANON_NOTICE="Anonymized for double-blind review"

# Portable in-place sed across BSD (macOS) and GNU.
# Usage: apply_sed_to_files <sed expression> <find primary 1> [find primary 2...]
# The find primaries select files relative to PWD.
apply_sed() {
  local expr="$1"; shift
  find . "$@" -not -path './.lake/*' -not -path './third_party/*' \
    -not -path './.git/*' -print0 \
    | xargs -0 -I{} sed -E -i.anonbak "$expr" "{}"
  find . -type f -name '*.anonbak' -print0 | xargs -0 rm -f
}

echo "==> Anonymizing Lean file headers"
# Targets the standard prologue produced by Mathlib:
#   /-
#   Copyright (c) YYYY Some Name. All rights reserved.
#   Released under Apache 2.0 license as described in the file LICENSE.
#   Authors: Some Name, Other Name
#   -/
apply_sed \
  "s|^Copyright \\(c\\) ([0-9]+) .*\\.( All rights reserved\\.)?|Copyright (c) \\1 ${ANON_NOTICE}.|" \
  -type f -name '*.lean'
apply_sed \
  "s|^Authors:.*|Authors: ${ANON_NOTICE}|" \
  -type f -name '*.lean'

echo "==> Anonymizing GitHub URLs in source and docs"
REMOTE_URL="$(cd "$REPO_ROOT" && git remote get-url "$REMOTE" 2>/dev/null || true)"
REMOTE_SLUG=""
case "$REMOTE_URL" in
  git@github.com:*)
    REMOTE_SLUG="${REMOTE_URL#git@github.com:}"
    REMOTE_SLUG="${REMOTE_SLUG%.git}"
    ;;
  https://github.com/*)
    REMOTE_SLUG="${REMOTE_URL#https://github.com/}"
    REMOTE_SLUG="${REMOTE_SLUG%.git}"
    ;;
esac
if [[ -n "$REMOTE_SLUG" ]]; then
  ESCAPED_REMOTE_SLUG="$(printf '%s\n' "$REMOTE_SLUG" | sed -E 's#[][\/.^$*+?{}()|]#\\&#g')"
  apply_sed \
    "s|https://github\\.com/${ESCAPED_REMOTE_SLUG}[A-Za-z0-9_/.#-]*|<anonymized-repo-url>|g; s|${ESCAPED_REMOTE_SLUG}|<anonymized>/<repo>|g" \
    -type f \( -name '*.lean' -o -name '*.md' -o -name '*.toml' -o -name '*.sh' -o -name '*.py' -o -name '*.yml' -o -name '*.yaml' \)
fi
apply_sed \
  "s|https://github\\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+[A-Za-z0-9_/.#-]*|<anonymized-repo-url>|g" \
  -type f \( -name '*.lean' -o -name '*.md' -o -name '*.toml' -o -name '*.sh' -o -name '*.py' -o -name '*.yml' -o -name '*.yaml' \)

echo "==> Scrubbing README paragraphs that link to removed files"
if [[ -f README.md ]]; then
  awk 'BEGIN{RS=""; ORS="\n\n"} \
       !/AGENTS\.md|CONTRIBUTING\.md|docs\/agents/ {print}' \
       README.md > README.md.anonbak
  mv README.md.anonbak README.md
fi

echo "==> Self-preserving the anonymization script in the snapshot"
mkdir -p scripts
cp "$SCRIPT_PATH" scripts/anonymize-for-submission.sh
chmod +x scripts/anonymize-for-submission.sh

echo "==> Committing single anonymized snapshot"
git add -A
SOURCE_SHA="$(cd "$REPO_ROOT" && git rev-parse "$SOURCE_REF")"
SHORT_SHA="${SOURCE_SHA:0:12}"
git -c user.name='Anonymous Authors' \
    -c user.email='anonymous@example.invalid' \
    commit -q -m "Anonymized snapshot of ${SOURCE_REF_NAME} @ ${SHORT_SHA} for CCS 2026 (Cycle B)"

if [[ "$DRY_RUN" -eq 1 ]]; then
  echo
  echo "Dry run complete. Anonymized commit lives only in temp worktree:"
  echo "  $TMP_WT (branch $TMP_BRANCH)"
  exit 0
fi

echo "==> Force-pushing temp branch to $REMOTE/$TARGET_BRANCH"
# Push from the temp branch directly to the remote target ref. We do not
# update the local $TARGET_BRANCH ref because it is likely checked out in
# another worktree and git refuses to force-update a checked-out branch.
# Local refresh happens in the next step via `git reset --hard`.
cd "$REPO_ROOT"
git push --force-with-lease="${TARGET_BRANCH}" \
    "$REMOTE" "${TMP_BRANCH}:refs/heads/${TARGET_BRANCH}"

echo "==> Refreshing any local worktree on $TARGET_BRANCH"
git fetch "$REMOTE" "$TARGET_BRANCH"
# Find the worktree (if any) currently checked out on $TARGET_BRANCH and
# fast-forward / reset it to the new tip so the user does not have to.
TARGET_WT="$(git worktree list --porcelain \
  | awk -v b="refs/heads/${TARGET_BRANCH}" '
      /^worktree / { wt = substr($0, 10) }
      $1 == "branch" && $2 == b { print wt }')"
if [[ -n "$TARGET_WT" ]]; then
  echo "    Resetting $TARGET_WT to ${REMOTE}/${TARGET_BRANCH}"
  git -C "$TARGET_WT" reset --hard "${REMOTE}/${TARGET_BRANCH}"
fi

echo
echo "Done. Anonymized snapshot of ${SOURCE_REF_NAME} @ ${SHORT_SHA}"
echo "is now at ${REMOTE}/${TARGET_BRANCH}."
