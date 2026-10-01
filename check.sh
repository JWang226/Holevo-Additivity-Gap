#!/usr/bin/env bash
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
# Rebuild every module, reject unproved dependencies, and retain the verification log.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .lake
./build.sh "$@" 2>&1 | tee .lake/check.log
if ! grep -q '^AUDIT PASSED:' .lake/check.log; then
  echo 'Verification failed: audit completion was not recorded.' >&2
  exit 1
fi
