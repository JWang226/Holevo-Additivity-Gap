#!/usr/bin/env bash
# Copyright (c) 2026 Free Entropy formalization contributors.
# Original QMDL attribution/licensing: https://github.com/JWang226/QMDL/blob/fd36df94068299e3d5e0bb193d19649319a40422/NOTICE
# Copyright (c) 2026 the Nonadditivity project contributors (adaptations).
# See COPYRIGHT.md for this project’s attribution and licensing status.
# Adapted for Holevo-Additivity-Gap from JWang226/QMDL at fd36df94068299e3d5e0bb193d19649319a40422; original attribution retained.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: bash scripts/verify.sh [all|lean|comparator|nanoda] [--nanoda-bin /absolute/path]
                              [--source-certificate REPO_RELATIVE_JSON]

  all         Build/audit Lean, compare statements/replay in Lean, then run Nanoda.
  lean        Fetch the locked mathlib cache, build All, and audit proof axioms.
  comparator  Compare all six expected-statement configurations and replay in Lean.
  nanoda      Run acceptance/rejection controls and all seven Nanoda theorem roots.

The default mode is all. Comparator and Nanoda run unsandboxed on trusted sources.
--source-certificate is optional and valid only for lean/all. It selects recorded
current-source evidence for both Lean release validations; omission preserves the
strict historical baseline check. The certificate path must name a local .json file.
Nanoda is built from the recorded source/Rust pins unless --nanoda-bin is supplied.
The supplied-binary option is valid only for all/nanoda; its provenance is the
caller's responsibility. Every run creates fresh logs under .verify-work/run-*.
The wrapper exits nonzero on any failure. It never invokes Linux sandbox checks.
EOF
}

die() { printf 'ERROR: %s\n' "$*" >&2; exit 2; }
mode=all
mode_seen=false
nanoda_bin=
source_certificate=
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    all|lean|comparator|nanoda)
      [[ "$mode_seen" == false ]] || die "Choose exactly one mode."
      mode=$1
      mode_seen=true
      shift ;;
    --nanoda-bin)
      [[ $# -ge 2 && -n "$2" ]] || die "--nanoda-bin requires an absolute path."
      [[ -z "$nanoda_bin" ]] || die "--nanoda-bin may be supplied only once."
      nanoda_bin=$2
      shift 2 ;;
    --source-certificate)
      [[ $# -ge 2 && -n "$2" ]] || die "--source-certificate requires a repository-relative JSON path."
      [[ -z "$source_certificate" ]] || die "--source-certificate may be supplied only once."
      source_certificate=$2
      shift 2 ;;
    *) die "Unknown argument: $1 (use --help)." ;;
  esac
done
if [[ -n "$nanoda_bin" ]]; then
  [[ "$mode" == all || "$mode" == nanoda ]] || die "--nanoda-bin requires all or nanoda mode."
  [[ "$nanoda_bin" == /* ]] || die "--nanoda-bin must be an absolute path."
  [[ -f "$nanoda_bin" && -x "$nanoda_bin" ]] || die "Nanoda binary is not an executable file: $nanoda_bin"
fi

if [[ -n "$source_certificate" ]]; then
  [[ "$mode" == all || "$mode" == lean ]] || die "--source-certificate requires all or lean mode."
fi

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$repo_root"
if [[ -n "$source_certificate" ]]; then
  command -v python3 >/dev/null 2>&1 || die 'Python 3 is required to validate the certificate path.'
  python3 - "$repo_root" "$source_certificate" <<'PY_CERTIFICATE_PATH' || die 'Invalid --source-certificate path.'
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
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
for required in python3 git lake; do
  command -v "$required" >/dev/null 2>&1 || die "Missing $required; see docs/verify.md prerequisites."
done
python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else "Python 3.11 or newer is required.")'
if [[ ( "$mode" == all || "$mode" == nanoda ) && -z "$nanoda_bin" ]]; then
  for required in rustup cargo; do
    command -v "$required" >/dev/null 2>&1 || die "Missing $required; install Rustup or supply --nanoda-bin."
  done
fi

mkdir -p .verify-work
run_dir=$(mktemp -d "$repo_root/.verify-work/run-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX")
current_stage=setup
finish_run() {
  local status=$?
  if [[ "$status" -ne 0 ]]; then
    printf 'VERIFICATION FAILED: %s (stage %s, exit %s)\n' "$mode" "$current_stage" "$status" \
      | tee "$run_dir/result.txt" >&2
    printf 'Logs: %s\n' "$run_dir" >&2
  fi
  return "$status"
}
trap finish_run EXIT
python3 - "$run_dir" "$mode" "$nanoda_bin" "$source_certificate" <<'PY'
import datetime, json, pathlib, sys
directory, mode, binary, source_certificate = sys.argv[1:]
pathlib.Path(directory, "run-info.json").write_text(json.dumps({
    "started_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "mode": mode,
    "sandboxed": False,
    "nanoda_binary_source": ("not_requested" if mode not in ("all", "nanoda")
                             else "caller_supplied" if binary else "build_from_recorded_pin"),
    "supplied_nanoda_binary": binary or None,
    "source_certificate": source_certificate or None,
    "note": "Invocation metadata only; success requires the requested stages to complete.",
}, indent=2) + "\n")
PY
printf 'Verification mode: %s\nFresh logs: %s\n' "$mode" "$run_dir"
printf '%s\n' 'Comparator and Nanoda are unsandboxed; use only trusted local sources.'

run_stage() {
  current_stage=$1
  shift
  printf '\nRunning %s\n' "$current_stage"
  # pipefail preserves checker failure even when tee successfully writes the log.
  "$@" 2>&1 | tee "$run_dir/$current_stage.log"
  printf 'STAGE PASSED: %s\n' "$current_stage"
}

if [[ "$mode" == all || "$mode" == lean ]]; then
  lean_command=(./verification/lean/run.sh)
  if [[ -n "$source_certificate" ]]; then
    lean_command+=(--source-certificate "$source_certificate")
  fi
  run_stage lean "${lean_command[@]}"
fi

if [[ "$mode" == comparator || "$mode" == nanoda ]]; then
  run_stage dependency-cache lake exe cache get
fi

if [[ "$mode" == all || "$mode" == comparator ]]; then
  run_stage comparator python3 verification/comparator/check_local.py --report "$run_dir/comparator-result.json"
fi

if [[ "$mode" == all || "$mode" == nanoda ]]; then
  if [[ -z "$nanoda_bin" ]]; then
    run_stage nanoda-build python3 - verification/nanoda/toolchain.json "$run_dir/nanoda-source" <<'PY'
import hashlib, json, os, pathlib, subprocess, sys, tomllib

pin = json.loads(pathlib.Path(sys.argv[1]).read_text())
source = pathlib.Path(sys.argv[2])
# Match the already documented, unmodified checker and compiler versions.
if (pin["repository"] != "https://github.com/ammkrn/nanoda_lib.git"
        or pin["commit"] != "3a2407216ee84a75f9e1aead6803d0578be06ae7"
        or pin["rust_toolchain"] != "1.90.0"):
    raise SystemExit("Unsupported Nanoda/Rust pin; review the wrapper before changing versions.")

def run(*args, **kwargs):
    subprocess.run(args, check=True, **kwargs)

run("git", "clone", pin["repository"], str(source))
run("git", "-C", str(source), "checkout", "--detach", pin["commit"])
revision = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
if revision != pin["commit"]:
    raise SystemExit("Nanoda source revision differs from the pin.")
if hashlib.sha256((source / "Cargo.lock").read_bytes()).hexdigest() != pin["cargo_lock_sha256"]:
    raise SystemExit("Nanoda Cargo.lock differs from the pin.")
if tomllib.loads((source / "Cargo.toml").read_text())["package"]["version"] != pin["package_version"]:
    raise SystemExit("Nanoda package version differs from the pin.")
run("rustup", "toolchain", "install", pin["rust_toolchain"], "--profile", "minimal")
rust_version = subprocess.check_output(
    ["rustc", "+" + pin["rust_toolchain"], "--version", "--verbose"], text=True)
if "commit-hash: " + pin["rust_commit"] not in rust_version:
    raise SystemExit("Rust compiler revision differs from the pin.")
print("Verified source, package, Cargo.lock and Rust pins.", flush=True)
environment = os.environ.copy()
environment["CARGO_TARGET_DIR"] = str(source / "target")
run("cargo", "+" + pin["rust_toolchain"], "build", "--release", "--locked",
    "--manifest-path", str(source / "Cargo.toml"), env=environment)
if subprocess.check_output(["git", "-C", str(source), "status", "--porcelain", "--untracked-files=no"], text=True).strip():
    raise SystemExit("Nanoda build changed tracked source files.")
binary = source / pin["binary"]
receipt = {"source": str(source.resolve()), "pin": pin,
           "rust_version": rust_version.strip(),
           "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest()}
(source.parent / "nanoda-build.json").write_text(json.dumps(receipt, indent=2) + "\n")
PY
    nanoda_bin="$run_dir/nanoda-source/target/release/nanoda_bin"
    nanoda_build_receipt="$run_dir/nanoda-build.json"
  else
    nanoda_build_receipt=
    printf '%s\n' 'Using caller-supplied Nanoda; this run does not establish its source/build provenance.' \
      | tee "$run_dir/nanoda-binary-source.txt"
  fi
  run_stage nanoda-controls python3 scripts/test_nanoda_check.py --lake-project . --nanoda-bin "$nanoda_bin"
  run_stage nanoda python3 verification/nanoda/check_nanoda.py --nanoda-bin "$nanoda_bin" \
    --report "$run_dir/nanoda-result.json" ${nanoda_build_receipt:+--build-receipt "$nanoda_build_receipt"}
fi

current_stage=complete
printf 'VERIFICATION PASSED: %s\n' "$mode" | tee "$run_dir/result.txt"
printf 'Logs and new reports: %s\n' "$run_dir"
