#!/usr/bin/env bash
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
# Reproduce the complete project-source build, axiom audit, and release checks.
set -euo pipefail

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$project_dir"

usage() {
  cat <<'HELP'
Usage: ./verification/lean/run.sh [--check-prerequisites | --help]
                                  [--source-certificate REPO_RELATIVE_JSON]

Requires Linux or macOS, Bash, Git, elan, and Python 3.11 or later with venv/pip.
Install elan from https://github.com/leanprover/elan and add ~/.elan/bin to PATH.
On Debian/Ubuntu, Python's venv support may require the python3-venv package.

The default run installs the toolchain in lean-toolchain, downloads the pinned
mathlib cache, and installs requirements-validation.txt in .verify-work/python-env.
It rebuilds every project proof module, audits transitive axioms, validates the
metadata/declaration mapping, and checks all six challenge modules locally.
It never runs lake update. This is a Lean check; it does not run Comparator.
--source-certificate optionally selects recorded current-source evidence for both
release validations. Without it, strict historical baseline validation is retained.
The path must name a repository-relative local .json file.

Results and logs: .verify-work/logs/lean-<UTC timestamp>-<process ID>/
Any failed step returns a nonzero exit code. --check-prerequisites downloads
nothing, builds nothing, and does not claim that any proof was verified.
HELP
}

fail() { printf 'Lean reproduction stopped: %s\n' "$*" >&2; exit 2; }
check_prerequisites=false
source_certificate=
while [[ $# -gt 0 ]]; do
  case "$1" in
    --help) usage; exit 0 ;;
    --check-prerequisites)
      [[ "$check_prerequisites" == false ]] || fail "--check-prerequisites may be supplied only once."
      check_prerequisites=true
      shift ;;
    --source-certificate)
      [[ $# -ge 2 && -n "$2" ]] || fail "--source-certificate requires a repository-relative JSON path."
      [[ -z "$source_certificate" ]] || fail "--source-certificate may be supplied only once."
      source_certificate=$2
      shift 2 ;;
    *) usage >&2; fail "Unknown argument: $1" ;;
  esac
done
case "$(uname -s)" in Linux|Darwin) ;; *) fail 'Linux or macOS is required.' ;; esac
command -v git >/dev/null || fail 'Git is missing.'
if [[ -d "$HOME/.elan/bin" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
command -v elan >/dev/null || fail 'elan is missing; see --help for installation.'
if command -v python3.11 >/dev/null; then
  repro_python=$(command -v python3.11)
elif command -v python3 >/dev/null; then
  repro_python=$(command -v python3)
else
  fail 'Python 3.11 or later is missing.'
fi
"$repro_python" -c 'import ensurepip, sys, venv; sys.exit(0 if sys.version_info >= (3, 11) else 1)' \
  || fail 'Python 3.11 or later with venv/pip is required.'
if [[ -n "$source_certificate" ]]; then
  "$repro_python" - "$project_dir" "$source_certificate" <<'PY_CERTIFICATE_PATH' || fail 'Invalid --source-certificate path.'
from pathlib import Path, PurePosixPath
import sys
root = Path(sys.argv[1]).resolve()
name = sys.argv[2]
relative = PurePosixPath(name)
if (relative.is_absolute() or "\\" in name or ":" in name
        or any(part in {"", ".", ".."} for part in name.split("/"))
        or relative.suffix != ".json"):
    raise SystemExit("Use a normalized repository-relative .json path.")
path = root / name
try:
    if not path.is_file():
        raise ValueError("not a regular file")
    path.resolve().relative_to(root)
except (ValueError, OSError, RuntimeError):
    raise SystemExit("Missing or nonlocal certificate JSON file: " + name)
PY_CERTIFICATE_PATH
fi
if [[ "$check_prerequisites" == true ]]; then
  printf '%s\n' 'Lean prerequisites found. No proof verification has run.'
  exit 0
fi

log_dir="$project_dir/.verify-work/logs/lean-$(date -u +%Y%m%dT%H%M%SZ)-$$"
mkdir -p "$log_dir"
cp lean-toolchain lake-manifest.json "$log_dir/"
printf 'running\n' > "$log_dir/status.txt"
finish() {
  repro_status=$?
  trap - EXIT
  set +e
  if [[ $repro_status -eq 0 ]]; then
    printf 'passed\n' > "$log_dir/status.txt"
  else
    printf 'failed (exit %s)\n' "$repro_status" > "$log_dir/status.txt"
  fi
  # On failure, the current step's log is already retained. Copy reports only
  # after a complete pass, so stale reports from earlier runs are not presented.
  if [[ $repro_status -eq 0 ]]; then
    for path in .lake/check.log .lake/release-validation.json .lake/release-declarations.log .lake/challenge-checks.json; do
      [[ ! -f "$path" ]] || cp "$path" "$log_dir/"
    done
    [[ ! -d .lake/challenge-checks ]] || cp -R .lake/challenge-checks "$log_dir/"
  fi
  printf 'Lean reproduction exit code: %s\nLogs: %s\n' "$repro_status" "$log_dir"
  exit "$repro_status"
}
trap finish EXIT
run_step() {
  step_name=$1
  shift
  printf '\n[%s]\n' "$step_name"
  printf '%q ' "$@" > "$log_dir/$step_name.command.txt"
  printf '\n' >> "$log_dir/$step_name.command.txt"
  if "$@" 2>&1 | tee "$log_dir/$step_name.log"; then
    step_status=0
  else
    step_status=$?
  fi
  printf '%s\n' "$step_status" > "$log_dir/$step_name.exit-code.txt"
  return "$step_status"
}
check_manifest() {
  cmp -s lake-manifest.json "$log_dir/lake-manifest.json" \
    || fail 'lake-manifest.json changed; restore the committed manifest before retrying.'
}

toolchain=$(tr -d '\r\n' < lean-toolchain)
git rev-parse HEAD > "$log_dir/project-commit.txt"
git status --short > "$log_dir/project-worktree.txt"
run_step platform uname -a
run_step python-version "$repro_python" --version
run_step elan-version elan --version
run_step python-environment "$repro_python" -m venv .verify-work/python-env
export PATH="$project_dir/.verify-work/python-env/bin:$PATH"
run_step validator-dependencies python3 -m pip install -r requirements-validation.txt
validator_command=(python3 scripts/validate_release.py)
if [[ -n "$source_certificate" ]]; then
  validator_command+=("--source-certificate=$source_certificate")
fi
run_step static-release "${validator_command[@]}" --static-only
run_step install-toolchain elan toolchain install "$toolchain"
run_step lean-version elan run "$toolchain" lean --version
run_step dependency-cache elan run "$toolchain" lake exe cache get
check_manifest
# Select the same compiler for the offline wrapper, including custom ELAN_HOME.
lean_prefix=$(elan run "$toolchain" lean --print-prefix)
export NONADDITIVITY_LEAN="$lean_prefix/bin/lean"
run_step proof-build-and-audit ./check.sh
run_step metadata-declarations "${validator_command[@]}"
run_step challenge-statements python3 scripts/check_challenges.py
check_manifest
printf '\nLEAN REPRODUCTION PASSED. Comparator was not run.\n'
