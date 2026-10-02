#!/usr/bin/env bash
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
# Run the pinned upstream Comparator using real Landrun and the systemd guard.
set -euo pipefail

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$project_dir"
comparator_revision=a4f696825c583ed8a5b4060d9a0faa5b882d365b
comparator_dir="$project_dir/.verify-work/comparator"

usage() {
  cat <<'HELP'
Usage: ./verification/comparator/run.sh [--check-prerequisites | --help]

Requires Linux, an unprivileged user, Git, elan, Python 3.11 or later, real
landrun built from upstream source, and a working systemd user session.
Install elan: https://github.com/leanprover/elan
Install landrun: https://github.com/Zouuup/landrun#installation
Sandbox guidance: https://github.com/leanprover/comparator#readme

The default run installs the pinned Lean toolchain, obtains the trusted mathlib
cache, and builds Comparator plus lean4export from their committed revisions in
.verify-work/comparator/. It checks all five JSON configurations under the
upstream-recommended systemd AF_UNIX guard, retaining one log per configuration.
It never runs lake update or substitutes an unsandboxed fake landrun.
The configurations use Lean kernel replay; additional nanoda checking is disabled.

For independent checking, use a fresh checkout, review the challenge statements
and their trusted imports, and run this script before compiling the proof sources
outside the sandbox. The mathlib cache is trusted dependency material.

Results and logs: .verify-work/logs/comparator-<UTC timestamp>-<process ID>/
Any failed step returns a nonzero exit code. --check-prerequisites downloads
nothing, builds nothing, and does not claim Comparator verification.
HELP
}

case "${1:-}" in
  --help) usage; exit 0 ;;
  ""|--check-prerequisites) ;;
  *) usage >&2; exit 2 ;;
esac
[[ $# -le 1 ]] || { usage >&2; exit 2; }

fail() { printf 'Comparator reproduction stopped: %s\n' "$*" >&2; exit 2; }
[[ "$(uname -s)" == Linux ]] || fail 'real Landrun requires Linux; see --help.'
[[ "$(id -u)" != 0 ]] || fail 'run as an unprivileged user, as required by upstream.'
if [[ -d "$HOME/.elan/bin" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
for executable in git elan landrun systemd-run systemctl; do
  command -v "$executable" >/dev/null || fail "$executable is missing; see --help."
done
systemctl --user show-environment >/dev/null \
  || fail 'a working systemd user session is required.'
if command -v python3.11 >/dev/null; then
  repro_python=$(command -v python3.11)
elif command -v python3 >/dev/null; then
  repro_python=$(command -v python3)
else
  fail 'Python 3.11 or later is missing.'
fi
"$repro_python" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' \
  || fail 'Python 3.11 or later is required.'
if [[ "${1:-}" == --check-prerequisites ]]; then
  printf '%s\n' 'Comparator prerequisites found. Sandbox capability and proofs have not been checked.'
  exit 0
fi

log_dir="$project_dir/.verify-work/logs/comparator-$(date -u +%Y%m%dT%H%M%SZ)-$$"
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
  printf 'Comparator reproduction exit code: %s\nLogs: %s\n' "$repro_status" "$log_dir"
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
check_manifests() {
  cmp -s lake-manifest.json "$log_dir/lake-manifest.json" \
    || fail 'the project lake-manifest.json changed; restore it before retrying.'
  if [[ -f "$log_dir/comparator-lake-manifest.json" ]]; then
    cmp -s "$comparator_dir/lake-manifest.json" "$log_dir/comparator-lake-manifest.json" \
      || fail 'the Comparator manifest changed; restore its pinned version before retrying.'
  fi
}

git rev-parse HEAD > "$log_dir/project-commit.txt"
git status --short > "$log_dir/project-worktree.txt"
run_step platform uname -a
run_step python-version "$repro_python" --version
run_step elan-version elan --version
# Record the actual external sandbox executable for anyone reviewing the logs.
"$repro_python" - "$(command -v landrun)" > "$log_dir/landrun.json" <<'PY'
import hashlib, json, pathlib, sys
path = pathlib.Path(sys.argv[1]).resolve()
print(json.dumps({"executable": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}, indent=2))
PY
toolchain=$(tr -d '\r\n' < lean-toolchain)
run_step install-toolchain elan toolchain install "$toolchain"
run_step lean-version elan run "$toolchain" lean --version
comparator_new_checkout=false
if [[ ! -d "$comparator_dir" ]]; then
  run_step clone-comparator git clone --no-checkout https://github.com/leanprover/comparator.git "$comparator_dir"
  comparator_new_checkout=true
fi
[[ "$(git -C "$comparator_dir" remote get-url origin)" == https://github.com/leanprover/comparator.git ]] \
  || fail 'the existing Comparator checkout has an unexpected origin.'
if [[ "$comparator_new_checkout" == false ]]; then
  [[ -z "$(git -C "$comparator_dir" status --porcelain --untracked-files=no)" ]] \
    || fail 'the existing Comparator checkout has tracked changes; use a clean checkout.'
fi
if ! git -C "$comparator_dir" cat-file -e "$comparator_revision^{commit}" 2>/dev/null; then
  run_step fetch-comparator git -C "$comparator_dir" fetch origin "$comparator_revision"
fi
run_step pin-comparator git -C "$comparator_dir" checkout --detach "$comparator_revision"
git -C "$comparator_dir" rev-parse HEAD > "$log_dir/comparator-commit.txt"
cmp -s lean-toolchain "$comparator_dir/lean-toolchain" \
  || fail 'the project and Comparator toolchains differ.'
cp "$comparator_dir/lake-manifest.json" "$log_dir/comparator-lake-manifest.json"
"$repro_python" - "$comparator_dir/lake-manifest.json" <<'PY'
import json, pathlib, sys
packages = {p["name"]: p["rev"] for p in json.loads(pathlib.Path(sys.argv[1]).read_text())["packages"]}
expected = {"lean4export": "048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d", "Lean4Checker": "b7398199245524275543dec6113229c9bb4902e5"}
if packages != expected:
    sys.exit("The pinned Comparator dependency revisions do not match.")
PY
run_step build-comparator bash -c 'cd "$1"; elan run "$2" lake build comparator lean4export' \
  bash "$comparator_dir" "$toolchain"
check_manifests
run_step dependency-cache elan run "$toolchain" lake exe cache get
check_manifests
export PATH="$comparator_dir/.lake/packages/lean4export/.lake/build/bin:$PATH"
export NONADDITIVITY_COMPARATOR_BIN="$comparator_dir/.lake/build/bin/comparator"
[[ -x "$NONADDITIVITY_COMPARATOR_BIN" ]] || fail 'the Comparator executable was not produced.'
command -v lean4export >/dev/null || fail 'the pinned lean4export executable was not produced.'
configs=(ComparatorChallenges/*.json)
[[ ${#configs[@]} -eq 5 ]] || fail 'exactly five challenge configurations are required.'
mkdir -p "$log_dir/configurations"
cp "${configs[@]}" "$log_dir/configurations/"
for config in "${configs[@]}"; do
  name=$(basename "$config" .json)
  # --pipe preserves stdout/stderr in the log; the upstream sandbox guard is
  # unchanged from its interactive --pty command.
  run_step "$name" systemd-run --user --pipe --wait --collect \
    --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$project_dir" \
    -E PATH="$PATH" -E NONADDITIVITY_COMPARATOR_BIN="$NONADDITIVITY_COMPARATOR_BIN" -- \
    bash -c 'elan run "$1" lake env "$NONADDITIVITY_COMPARATOR_BIN" "$2"' bash "$toolchain" "$config"
  run_step "$name-completion" "$repro_python" - "$log_dir/$name.log" <<'PY'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
# Remove ANSI control sequences before comparing a complete output line.
text = re.sub(r"\x1b\][^\x07]*(?:\x07|\x1b\\)", "", text)
text = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", text)
if not any(line.strip() == "Your solution is okay!" for line in text.splitlines()):
    sys.exit("Comparator exited without its success marker; verification is incomplete.")
print("Comparator success marker confirmed.")
PY
done
check_manifests
printf '\nCOMPARATOR REPRODUCTION PASSED: five configurations. Nanoda was not run.\n'
