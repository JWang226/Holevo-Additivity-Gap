<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Reproduce the verification

The portable workflow follows [QMDL](https://github.com/JWang226/QMDL). It works on macOS and Linux without landrun or systemd.

For this release, Lean and `all` use the explicit current-source certificate shown below. The certificate selects recorded rebuild/type evidence; both commands still rebuild and audit the project sources. Without it, the validator retains the strict historical byte-equality gate. [Cleanup evidence and elaboration reproduction](ELABORATION_CLEANUP.md) explain the certificate's Lean/type-only scope; historical portable reports retain their original bindings.

## Prerequisites

Install Bash, Git, [elan](https://github.com/leanprover/elan), Python 3.11 or newer with `venv`/`pip`, and native C/C++ build tools. Nanoda’s pinned-source build also needs [Rustup](https://rustup.rs/). Add `~/.elan/bin` and, when using Rustup, `~/.cargo/bin` to `PATH`. On macOS, the compiler is supplied by Xcode Command Line Tools (`xcode-select --install`); on Debian/Ubuntu, install `build-essential` and `python3-venv`. Network access is needed to download pinned dependencies.

Lean is pinned to `4.29.0-rc6`, Mathlib to the committed `lake-manifest.json`, and the checker revisions are recorded below. The wrapper never runs `lake update`. A full project-source rebuild can take considerable time; the dependency Mathlib cache is downloaded rather than rebuilt from source.

## Get the repository

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git
cd Holevo-Additivity-Gap
```

The default branch is `main`. To reproduce a particular published release,
check out its actual tag or commit before running the commands below.

## Run checks separately

Each mode prepares its own dependencies and builds the proof modules it needs. Run your chosen command from the repository root; no prior `all` run is required.

### Lean

```sh
bash scripts/verify.sh lean \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

Rebuilds all 369 project modules, audits 9,107 declarations, validates manuscript mappings, and checks six local challenge types. Rust is not required.

### Comparator

```sh
bash scripts/verify.sh comparator
```

Exports expected statements and actual proofs for all five configurations, compares types and referenced definitions using pinned Comparator, enforces the axiom policy, and replays exports through Lean’s kernel. Rust is not required.

### Nanoda

```sh
bash scripts/verify.sh nanoda
```

Builds pinned Nanoda, runs acceptance/rejection controls, and checks all six solution theorem roots through the independent Rust kernel. Run Comparator as well for comparison with the expected statements.

## Run all checks

```sh
bash scripts/verify.sh all \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

`all` is also the default when the mode is omitted; the current cleanup sources still need the explicit certificate option. All requested stages must finish successfully before the wrapper prints `VERIFICATION PASSED: all`. Any failed stage returns a nonzero exit code and retains its log. Use `bash scripts/verify.sh --help` for usage.

The existing `verification/lean/run.sh`, `verification/comparator/run.sh`, and `verification/nanoda/run.sh` entry points remain available. The latter two delegate to the portable workflow.

If Nanoda has already been built, optionally supply its executable:

```sh
bash scripts/verify.sh nanoda --nanoda-bin /absolute/path/to/nanoda_bin
```

Such a run records `caller_supplied` binary provenance. The default builds from the recorded source revision, locked Cargo dependencies, and Rust compiler, checks them, and records the binary hash and build receipt.

## Expected output and evidence

- Lean completes with `LEAN REPRODUCTION PASSED` and the full axiom audit marker.
- Comparator prints `LOCAL DIAGNOSTIC PASSED` for each of the five configurations.
- Nanoda’s controls accept a valid theorem and reject missing targets, non-theorem roots, forbidden axioms, `sorryAx`, and an ill-typed proof. The same control suite exercises Comparator, including mismatched expected statements.
- Nanoda prints `NANODA PASSED (UNSANDBOXED)` for each configuration.
- The wrapper ends with `VERIFICATION PASSED: <mode>` only after every requested stage passes.

Fresh logs are saved in `.verify-work/run-<UTC>-<unique suffix>/`. Comparator and Nanoda success reports record the five cases, six theorem names, tool pins, source and artifact hashes, and unsandboxed status. Each run uses fresh report paths; no earlier success report is reused. The Lean stage also retains detailed logs in `.verify-work/logs/lean-*`.

The [current full-run summary](../verification/portable-20261007/run-summary.json) records successful all-mode proof verification on source commit `38b36070`. The [overall GitHub job record](../verification/github-actions-release-all-38b36070.json) and [verbatim excerpt](../verification/github-actions-release-all-38b36070-excerpt.log) retain the later statement-recorder failure and skipped website step. [Normal Lean CI](../verification/github-actions-release-38b36070.json) also passed on that source commit. The [verification index](../verification/README.md) distinguishes these records from the preserved October 2 evidence and the narrower [cleanup build/type certificate](../verification/elaboration-20261006/README.md).

The completed Linux expected-statement applications and root-axiom probes were recovered from the hash-verified job artifact after the recorder rejected universe annotations in printed axiom names. These checks used the same fresh Linux project objects, whose declaration export matched the frozen metadata. No proof commands were rerun. The [recovery provenance](../verification/statement-audit-20261007/recovery.json) binds the original outputs and source commit; it explicitly records that the original recorder driver's argument list was not retained. Source/artifact hashes identify the exact checked inputs, including changes beyond a report's recorded base Git commit.

Check the retained release records' freshness:

```sh
python3 verification/check_reports.py
python3 verification/check_statement_audit.py
```

Both evidence checks pass for the release records. They validate selected
source, tool and evidence hashes without repeating proof checks or semantic
review. The [statement-review continuation](STATEMENT_AUDIT_DELTA.md) retains
six qualified findings and records its incremental exact-type and axiom checks
separately from the full build, Comparator and Nanoda run. It does not claim a
complete semantic audit, machine-certified English–Lean equivalence or
independent human certification.

## Tool pins

| Tool | Revision |
| --- | --- |
| Comparator | `a4f696825c583ed8a5b4060d9a0faa5b882d365b` |
| lean4export | `048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` |
| Lean4Checker | `b7398199245524275543dec6113229c9bb4902e5` |
| Nanoda 0.4.19 | `3a2407216ee84a75f9e1aead6803d0578be06ae7` |
| Rust 1.90.0 | `1159e78c4747b02ef996e55082b704c09b970588` |

The full Nanoda pin, including `Cargo.lock` SHA-256, is in [verification/nanoda/toolchain.json](../verification/nanoda/toolchain.json).

## Trust and scope

Comparator mode directly invokes the pinned comparison and axiom-checking APIs, followed by Lean kernel replay. Nanoda supplies an independent kernel implementation. Both run **unsandboxed on trusted local sources**. This workflow does not claim execution of the sandboxed upstream Comparator CLI.

Review the challenge import closures, definitions, and expected statements: they include lower-level project lemmas. Challenge files contain six intentional `sorry` placeholders for expected statements; these are excluded from the proof build and are never accepted as solution proofs. Solution axiom closures must contain only `propext`, `Classical.choice`, and `Quot.sound`.

Kernel checking establishes the formal statements. It does not establish the natural-language correspondence or formalize the entire manuscript. See [formalization scope](FORMALIZATION_STATUS.md) and [challenge trust assumptions](../ComparatorChallenges/README.md).
