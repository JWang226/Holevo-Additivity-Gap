#!/bin/sh
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
# Offline compiler wrapper. NONADDITIVITY_LEAN can select a compatible Lean executable.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
lean_path="$project_dir/.lake/build/lib/lean"
for package_dir in "$project_dir"/.lake/packages/*; do
  [ -d "$package_dir/.lake/build/lib/lean" ] || continue
  lean_path="$lean_path:$package_dir/.lake/build/lib/lean"
done
export LEAN_PATH="$lean_path${NONADDITIVITY_LEAN_PATH:+:$NONADDITIVITY_LEAN_PATH}"
if [ -n "${NONADDITIVITY_LEAN:-}" ]; then
  lean_bin=$NONADDITIVITY_LEAN
elif [ -x "$HOME/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean" ]; then
  lean_bin="$HOME/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean"
elif [ -x "$HOME/.elan/bin/lean" ]; then
  lean_bin="$HOME/.elan/bin/lean"
else
  lean_bin=lean
fi
cd "$project_dir"
mkdir -p "$project_dir/.lake"
exec python3 "$project_dir/scripts/compiler.py" "$lean_bin" "$project_dir/.lake/compiler.lock" "$@"
