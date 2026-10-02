#!/usr/bin/env bash
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
set -euo pipefail
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
exec bash "$project_dir/scripts/verify.sh" nanoda "$@"
