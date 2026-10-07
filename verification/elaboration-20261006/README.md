# Elaboration cleanup — October 6–7, 2026

Completed sequence: dead-code sweep → full elaboration test → guarded cleanup trials → second full elaboration test. Both complete tests ran on the same four-core Ubuntu 22.04 runner with Lean 4.29.0-rc6, GNU time, a serial project driver, and unchanged cached dependencies. [Successful workflow](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/37543825590).

| Complete project rebuild | Before | After | Change |
| --- | ---: | ---: | ---: |
| Wall time | 2,168.55 s | 2,162.44 s | −6.11 s (−0.28%) |
| CPU, user + system | 3,142.12 s | 3,136.81 s | −5.31 s (−0.17%) |
| Summed module CPU | 3,076.49 s | 3,068.31 s | −8.18 s (−0.27%) |
| Peak RSS, KiB | 4,531,316 | 4,537,440 | +6,124 (+0.14%) |
| Successfully compiled modules | 369 | 369 | 0 |
| Errors / proof holes | 0 / 0 | 0 / 0 | 0 |
| Existing warnings | 104 | 104 | 0 |
| Files taking at least 10 s | 23 | 22 | −1 |

These single full-build observations show almost unchanged aggregate cost. They do not establish a project-wide speedup. The repeated isolated trial provides the evidence for the retained local improvement.

## What changed

The dead-code sweep removed **50 redundant direct local imports in 40 files**, preserving every local transitive import closure. All 81 source-written private declarations had consumers; apparent unused private declarations were generated equation, splitter, simp or congruence helpers. No safe helper or whole-module deletion was found. The timed baseline already includes these import removals, so their performance contribution was not measured. [Sweep record](dead-code.json).

One elaboration edit was retained: give `Equiv.summable_iff` its explicit norm-power summand in `RegularCoefficientEnergy`. Three paired warm runs produced these medians:

| Retained trial | Before | After | Change |
| --- | ---: | ---: | ---: |
| Wall time | 17.92 s | 9.84 s | −45.09% |
| CPU | 22.03 s | 13.91 s | −36.86% |
| Tactic execution | 9.24 s | 1.14 s | −87.66% |
| Typeclass inference | 8.52 s | 8.51 s | Essentially unchanged |

The final full build independently measured this file at 18.09 → 9.73 s wall and 22.16 → 14.09 s CPU. Its final supplemental warm profile measured tactic execution at 9.29 → 1.20 s; checking rose only 0.018 s and import loading 0.06 s. No comparable cost transfer was observed.

A NetPolynomial type-ascription trial was valid but gave no qualifying improvement; it was reverted. A private Gram-helper extraction hit the existing heartbeat limit in all three candidate attempts; it was reverted, and failed timings are excluded from performance comparisons. No heartbeat or recursion policy changed. No class cache or speculative import-shrinking rewrite was retained.

## Read the reports

- [Detailed before/after comparison](comparison/ELABORATION_COMPARISON.md), with the complete 369-module join in [comparison.json](comparison/comparison.json): sizes, CPU/wall/RSS, warning census, heavy tiers, top 30, filename families, phases, large events, A/B decisions, and setup guards.
- [Original before report](before/ELABORATION_REPORT_2026-10-06_before.md) and [original after report](after/ELABORATION_REPORT_2026-10-07_after.md), each retaining all module timings and eight independently chosen worst-file profiles.
- [Baseline interpretation](BASELINE_FINDINGS.md) explains the phase routing and why the remaining large costs were not rewritten without measured evidence.
- [Reproducer commands](../../docs/ELABORATION_CLEANUP.md) repeat the exact snapshots, public-type check, and report generation.

The after test's original top eight remain unchanged. A separate [matched-profile supplement](matched-profiles/summary.json) supplies `RegularCoefficientEnergy`, which left that top eight after improvement. `UniversalFactorizationPolynomialDilation` enters the after top eight and has no before warm profile; it is explicitly unmatched.

Some individual counters increased: Audit's warm elaboration rose 251 → 253 s, and CSSkeletonDecoration tactic execution rose 1.52 → 1.71 s. Their sources are unchanged; these single observations do not establish cleanup-caused regressions. Every full-build module's wall and CPU increases stayed below both 2 s and 10%. The complete phase tables retain these variations rather than claiming all counters improved.

## Proof integrity and scope

Both full rebuilds audited **9,107 project declarations / 7,219 theorem constants**, with only `propext`, `Classical.choice`, and `Quot.sound`. The fresh [public-type comparison](public-types.json) passed for **all 5,323 public declarations and six challenge roots**, comparing exact identities, universe parameters and independently decoded canonical kernel-type bytes against reviewed commit `a92c087e85603032cd0ece7b766b1f192b17a69e`. All ten challenge/configuration files are unchanged.

The [source certificate](source-certificate.json) binds all 369 current proof files, the seven measured driver inputs, the complete rebuild/audit log, and that comparison. [Static release validation](source-validation.json) passed with the explicit certificate; its local Lean mapping/type check is recorded as `not_run`. The new Lean execution evidence is the Linux full rebuild and fresh export, not that static command.

This cleanup **did not rerun Comparator or Nanoda**, re-review English-to-Lean correspondence, or establish complete manuscript formalization. Existing historical portable and manuscript-review records keep their original bindings. Definition-body equivalence is outside the public-type comparison's scope.

The applied `lean-elaboration-test` and `lean-elaboration` skills are pinned to [LeanAutoformalizationSkills commit 70bb859](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills). Their modern `module`-header expectation remains **unmet in all 369 production files**. This is an explicit scope adaptation, not an unqualified pass of every skill criterion.

## Evidence and provenance

Measured baseline: `743cc95bc4c0b1bca891994def26d9e5f8c7aad6`. Measured final source: `e943a85f0234a573477a10871f60a2d9583fa47b`. The later publication commit adds evidence and tooling; it is not another timed snapshot. Main and the proof website retain the reviewed release.

Raw compiler/GNU time logs, source inventories, dependency and own-artifact manifests are preserved in `before/` and `after/`. Raw A/B records are in `trials/1/`, `trials/2/`, and `trials/3/`; explicit reviews are in `reviews/`, converted comparisons in `ab/`, and selection receipts in `trials/4/` and [final-selection.json](final-selection.json). [Initial continuation state](continuation-initial.json) binds the frozen tools and baseline objects. [GitHub provenance](github-run.json) and `download-receipts/` record the downloaded artifact and per-file hashes.

The current [declaration export](../../metadata/declarations.json) is the exact downloaded output. Raw exporter streams are retained in `declaration-export/`; the two large streams use deterministic gzip, with original and compressed hashes in [archive-receipt.json](declaration-export/archive-receipt.json). Decompression recovers their exact original bytes.

The cancelled macOS pilot and diagnostic probes are retained separately under `excluded-macos-pilot/` and `diagnostics/`. They are excluded from all Linux performance comparisons. A temporary-`sorry` diagnostic is explicitly non-production; both complete production builds permit no proof holes.
