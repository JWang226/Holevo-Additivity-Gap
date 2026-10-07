<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Reproduce the elaboration cleanup

The [cleanup evidence](../verification/elaboration-20261006/README.md) records
one full before build, three isolated A/B interventions, and one full after
build on the same Ubuntu 22.04 runner. The timed baseline already includes the
50 redundant-import removals. Their speed contribution was not measured.

## Repeat the full snapshots

Use a fresh checkout on Linux with Git, elan, Python 3.11+, GNU time and the
repository's normal native build prerequisites. The measured snapshots are
immutable commits, distinct from the later report/publication commit:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git Holevo-Additivity-Gap-elab
cd Holevo-Additivity-Gap-elab
git checkout --detach 743cc95bc4c0b1bca891994def26d9e5f8c7aad6
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
ELAB_REPRO_OUTPUT=$(mktemp -d)
python3 scripts/elaboration_test.py --label before \
  --output "$ELAB_REPRO_OUTPUT/before" --time-bin /usr/bin/time
git checkout --detach e943a85f0234a573477a10871f60a2d9583fa47b
python3 scripts/elaboration_test.py --label after \
  --output "$ELAB_REPRO_OUTPUT/after" --time-bin /usr/bin/time \
  --prior-summary "$ELAB_REPRO_OUTPUT/before/summary.json"
```

Both invocations recompile all 369 own modules through the existing serial
`build.sh` driver, then profile their own worst eight modules serially without
writing compiler artifacts. Lean keeps its default internal threading. Cached
Mathlib/dependency objects are inputs; neither `lake clean`, `lake update`, nor
an upstream source rebuild is part of the timed test. Setup is outside timing.
Do not change sources or build artifacts while a measurement is running.

A repeat run gives new observations, not the recorded numbers. Keep the same
host, compiler/time binaries, cache and scheduling policy for a comparable pair.
On macOS, supply an installed GNU time executable rather than BSD
`/usr/bin/time`; macOS timings are not interchangeable with the Linux evidence.

The [continuation protocol](LINUX_ELABORATION_PROTOCOL.md) documents the guarded
same-runner A/B procedure, six fixed request slots and source-only candidates.
For a new workflow run use a fresh control branch whose first request has
sequence 1. The historical control branch has already reached sequence 4.
Use the full baseline SHA above as `baseline_ref`; the cleanup publication
branch advances after measurement and is not an immutable baseline.

## Recheck proof and statement integrity

Switch from the detached measured snapshot to the cleanup publication branch;
the measured commit deliberately predates the certificate/report tooling. The
explicit certificate selects the current source evidence. The normal historical
baseline validation remains unchanged when the option is omitted:

```sh
git switch codex/cleanup-elaboration-20261006
bash scripts/verify.sh lean \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

This prepares pinned dependencies, performs a fresh full proof build/axiom
audit, then runs the normal manuscript-mapping and local challenge checks.
The certificate validates the archived Linux rebuild and all 5,323 public
canonical kernel types; it does not substitute for the new build.

After that build, independently re-export and compare current public types:

```sh
mkdir -p .verify-work
ELAB_TYPE_RECHECK=$(mktemp -d .verify-work/cleanup-recheck-XXXXXX)
python3 scripts/export_declarations.py --fresh \
  --output "$ELAB_TYPE_RECHECK/declarations.json"
python3 scripts/compare_public_types.py \
  --after-export "$ELAB_TYPE_RECHECK/declarations.json" \
  --report "$ELAB_TYPE_RECHECK/public-types.json"
```

Use a new report path on every run. The scratch export leaves the hash-bound
published `metadata/declarations.json` unchanged. Compression streams may differ
across zlib versions; the comparison independently decodes canonical type bytes.
It compares exact public names, roles, defining modules/files, universe parameters
and types against reviewed commit `a92c087e85603032cd0ece7b766b1f192b17a69e`.
All six challenge roots and ten challenge/configuration files are covered.

Comparator and Nanoda remain independently runnable:

```sh
bash scripts/verify.sh comparator
bash scripts/verify.sh nanoda
# Or perform fresh Lean, Comparator/replay and Nanoda checks together:
bash scripts/verify.sh all \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

The elaboration cleanup did not rerun Comparator or Nanoda. Earlier portable
records retain their historical source/checker bindings. The certificate is
explicitly limited to a Lean rebuild and exact public types; it does not claim
new English-to-Lean review or complete manuscript formalization.

## Regenerate the archived comparison

This command reads recorded measurements and committed sources; it runs no
compiler or proof checker. Run it from the cleanup publication branch:

```sh
mkdir -p .verify-work
ELAB_COMPARISON_RECHECK=$(mktemp -d .verify-work/cleanup-comparison-XXXXXX)
python3 scripts/compare_elaboration.py --repo . \
  --before verification/elaboration-20261006/before/summary.json \
  --after verification/elaboration-20261006/after/summary.json \
  --after-supplemental-profiles verification/elaboration-20261006/matched-profiles/summary.json \
  --dead-code-json verification/elaboration-20261006/dead-code.json \
  --api-check verification/elaboration-20261006/public-types.json \
  --ab-summary verification/elaboration-20261006/ab/trial-1.json \
  --ab-summary verification/elaboration-20261006/ab/trial-2.json \
  --ab-summary verification/elaboration-20261006/ab/trial-3.json \
  --output "$ELAB_COMPARISON_RECHECK"
```

The raw `trials/N/result.json` files and explicit `reviews/trial-N.json` records
are inputs to `scripts/convert_ab_trial.py`. Its `--help` lists the required
source/state/snapshot bindings. Trial 3 additionally needs
`--failed-intervention --decision reverted`; aborted candidate times are retained
only as diagnostics, with no candidate medians or speed comparison.

## Method and limitations

The applied skill files are `lean-elaboration-test/SKILL.md` and
`lean-elaboration/SKILL.md` from
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills).
The repository harness and report tools are original implementations of that
workflow. The modern `module`-header expectation is **unmet**: all 369 production
files remain in legacy syntax. This is a recorded scope adaptation, not a pass
of the skill's zero-legacy-files criterion. No file-size cap is introduced.
Existing heartbeat/recursion settings are inventoried; this cleanup changes none.

The two full snapshots are descriptive. Repeated isolated A/B supplies the
performance evidence for the retained summand annotation. Per-module GNU CPU
is user + system time; wall time and CPU totals are distinct. Profiler categories
are exclusive counters rather than a complete elapsed-time partition. Cached
artifact guards compare recorded stat provenance and cannot detect a mutation
perfectly restored between snapshots. Dedicated audit work is retained.

A cancelled macOS pilot and macOS diagnostic probes are excluded from the Linux
before/after measurements. The diagnostic probe with a temporary `sorry` is not
a production proof; both successful full builds permit no proof holes. Raw
source/checker hashes, commands and archive receipts identify the actual evidence.
