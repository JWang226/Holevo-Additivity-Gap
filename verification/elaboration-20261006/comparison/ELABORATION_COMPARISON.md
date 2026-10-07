# Elaboration cleanup: before and after

## Scope and sequence

The sequence was an initial dead-code sweep, a complete pre-elaboration baseline, measured elaboration interventions, and a second complete elaboration test. The timing comparison starts after the dead-code sweep; it does not measure that sweep's speed effect.

Initial source commit: `a92c087e85603032cd0ece7b766b1f192b17a69e`. Safe user-written private/helper deletions: **0**. Redundant direct local imports removed: **50** across **40** files. Whole modules removed: **0**.
All local import closures preserved: `True`. Sweep record's own status: `sweep_validated_by_complete_baseline_build`; the subsequent valid builds are separate evidence.

The verified build scope and six principal challenge roots do not establish full manuscript coverage or English-to-Lean equivalence. Existing attainment and representation qualifications remain separate mathematical scope limitations.

## Setup and provenance

| Field | Before | After |
| --- | --- | --- |
| commit | 743cc95bc4c0b1bca891994def26d9e5f8c7aad6 | e943a85f0234a573477a10871f60a2d9583fa47b |
| started_utc | 2026-10-06T22:59:47+00:00 | 2026-10-07T00:07:50+00:00 |
| finished_utc | 2026-10-06T23:43:40+00:00 | 2026-10-07T00:51:41+00:00 |
| host | runnervmwvtoz | runnervmwvtoz |
| platform | Linux-6.8.0-1064-azure-x86_64-with-glibc2.35 | Linux-6.8.0-1064-azure-x86_64-with-glibc2.35 |
| compiler_version | Lean (version 4.29.0-rc6, x86_64-unknown-linux-gnu, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release) | Lean (version 4.29.0-rc6, x86_64-unknown-linux-gnu, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release) |
| time_version | time (GNU Time) UNKNOWN | time (GNU Time) UNKNOWN |
| cores | 4 | 4 |
| driver_parallelism | 1 | 1 |
| lean_internal_threads | Compiler default; no -j override (same pinned compiler for both runs) | Compiler default; no -j override (same pinned compiler for both runs) |

Compiler and GNU time hashes, host, core count, driver parallelism and Lean internal-thread policy match. The retained provenance reports the exact RSS interpretation and process-visibility availability. An unavailable process inventory is not evidence of an idle host.

## Size snapshot

| Scope | Before files | After files | Before physical lines | After physical lines | Before code lines | After code lines |
| --- | --- | --- | --- | --- | --- | --- |
| git_tree | 768 | 768 | 115995 | 115997 | 89728 | 89730 |
| git_build_scope | 369 | 369 | 57473 | 57475 | 44492 | 44494 |
| working_build_scope | 369 | 369 | 57473 | 57475 | 44492 | 44494 |

The full Git tree includes Lean files outside the production build. Cost per line uses the committed own build scope; comment-only files are excluded according to the measured snapshot.

## Headline timing and build health

| Metric | Before | After | Delta | Delta % |
| --- | --- | --- | --- | --- |
| wall_s | 2168.55 | 2162.44 | -6.11 | -0.28 |
| cpu_s | 3142.12 | 3136.81 | -5.31 | -0.17 |
| user_s | 2736.76 | 2730.20 | -6.56 | -0.24 |
| sys_s | 405.36 | 406.61 | 1.25 | 0.31 |
| percent_cpu | 144.00 | 145.00 | 1.00 | 0.69 |
| max_rss_raw | 4531316.00 | 4537440.00 | 6124.00 | 0.14 |
| summed own cpu_s | 3076.490 | 3068.310 | -8.180 | -0.27 |
| summed own observed_cpu_parallelism | 1.419 | 1.419 | 0.000 | 0.02 |

Module CPU is GNU user + system time. Every compiler invocation is timed, including jobs under one second. Full wall time includes startup and measurement-wrapper/guard overhead; compiler peak RSS is not additive. Read each snapshot's RSS interpretation before comparing to other platforms.

| Health | Before | After |
| --- | --- | --- |
| error_count | 0 | 0 |
| warning_count | 104 | 104 |
| sorry_warning_count | 0 | 0 |
| unauthorized_sorry_tokens | 0 | 0 |
| complete measured jobs | 369 | 369 |
| build exit | 0 | 0 |

Before warning census:

```json
{
  "Try `simp at hi` instead of `simpa using hi`": 1,
  "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice": 19,
  "deprecated declaration/syntax": 1,
  "try 'simp' instead of 'simpa'": 6,
  "unused variable/argument": 77
}
```

After warning census:

```json
{
  "Try `simp at hi` instead of `simpa using hi`": 1,
  "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice": 19,
  "deprecated declaration/syntax": 1,
  "try 'simp' instead of 'simpa'": 6,
  "unused variable/argument": 77
}
```

## Heavy tail and top 30

| Wall threshold | Before files | After files | Delta |
| --- | --- | --- | --- |
| ≥10s | 23 | 22 | -1 |
| ≥20s | 6 | 6 | 0 |
| ≥30s | 5 | 5 | 0 |
| ≥40s | 3 | 3 | 0 |

| Module | Before wall s | After wall s | Delta wall s | Before CPU s | After CPU s | Delta CPU s | Source changed |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Audit` | 261.22 | 260.64 | -0.58 | 261.64 | 261.05 | -0.59 | False |
| `Nonadditivity.NetPolynomial` | 62.05 | 61.75 | -0.30 | 102.88 | 101.64 | -1.24 | False |
| `Nonadditivity.RegularFactorization` | 48.29 | 48.41 | 0.12 | 146.38 | 146.49 | 0.11 | False |
| `Nonadditivity.InitialNetReduction` | 36.37 | 36.45 | 0.08 | 76.07 | 76.36 | 0.29 | False |
| `Nonadditivity.CollinsYounTensor` | 32.31 | 32.50 | 0.19 | 67.37 | 67.97 | 0.60 | False |
| `Nonadditivity.UniversalFactorizationGram` | 26.63 | 26.42 | -0.21 | 55.55 | 56.21 | 0.66 | False |
| `Nonadditivity.UniversalFactorizationPolynomialDilation` | 17.60 | 18.01 | 0.41 | 19.98 | 20.46 | 0.48 | False |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | 18.04 | 17.79 | -0.25 | 21.86 | 21.67 | -0.19 | False |
| `Nonadditivity.ProductMomentBridge` | 16.34 | 16.49 | 0.15 | 36.98 | 37.74 | 0.76 | False |
| `Nonadditivity.RegularFubini` | 16.32 | 16.08 | -0.24 | 24.04 | 23.62 | -0.42 | False |
| `Nonadditivity.RegularShiftedDilation` | 15.45 | 15.27 | -0.18 | 25.60 | 25.34 | -0.26 | False |
| `Nonadditivity.RegularDilation` | 14.49 | 15.00 | 0.51 | 34.09 | 33.52 | -0.57 | False |
| `Nonadditivity.FreeCreation` | 14.64 | 14.56 | -0.08 | 19.31 | 19.25 | -0.06 | False |
| `Nonadditivity.HaarOperatorPolynomial` | 14.81 | 14.54 | -0.27 | 21.36 | 20.99 | -0.37 | False |
| `Nonadditivity.CollinsYoun` | 14.48 | 14.40 | -0.08 | 31.69 | 31.82 | 0.13 | False |
| `Nonadditivity.ProductHaagerupWords` | 13.47 | 13.57 | 0.10 | 16.00 | 16.19 | 0.19 | False |
| `Nonadditivity.StructuredCostBounds` | 12.64 | 12.82 | 0.18 | 36.25 | 36.24 | -0.01 | False |
| `Nonadditivity.StructuredLinearization` | 12.74 | 12.63 | -0.11 | 15.73 | 15.60 | -0.13 | False |
| `Nonadditivity.Quantitative` | 12.25 | 12.30 | 0.05 | 35.79 | 35.99 | 0.20 | False |
| `Nonadditivity.HaarNonbacktracking` | 12.27 | 11.97 | -0.30 | 17.63 | 17.84 | 0.21 | False |
| `Nonadditivity.FreeModel` | 11.99 | 11.96 | -0.03 | 13.19 | 13.15 | -0.04 | False |
| `Nonadditivity.FiniteSetFactorization` | 11.47 | 11.64 | 0.17 | 21.16 | 21.11 | -0.05 | False |
| `Nonadditivity.RegularCoefficientEnergy` | 18.09 | 9.73 | -8.36 | 22.16 | 14.09 | -8.07 | True |
| `Nonadditivity.ProductHaagerupCreation` | 9.59 | 9.59 | 0.00 | 18.02 | 17.81 | -0.21 | False |
| `Nonadditivity.UniversalShiftedDilation` | 9.34 | 9.59 | 0.25 | 19.30 | 19.74 | 0.44 | False |
| `Nonadditivity.NoncommutativeCSCrossing` | 9.25 | 9.38 | 0.13 | 9.76 | 9.87 | 0.11 | False |
| `Nonadditivity.CollinsYounProduct` | 9.04 | 9.35 | 0.31 | 20.30 | 20.42 | 0.12 | False |
| `Nonadditivity.HaarNonbacktrackingRenewal` | 9.38 | 9.31 | -0.07 | 17.42 | 17.31 | -0.11 | False |
| `Nonadditivity.HaarWordExpansion` | 9.37 | 9.30 | -0.07 | 20.69 | 20.70 | 0.01 | False |
| `Nonadditivity.FiniteRealization` | 9.35 | 9.25 | -0.10 | 11.35 | 11.18 | -0.17 | False |

The table ranks the after build. All modules are joined by identity, including files outside the prior top 30; the complete joined inventory is in the accompanying JSON.

## File-family costs

| Filename prefix | Files | Before CPU s | After CPU s | Delta CPU s | Delta wall s |
| --- | --- | --- | --- | --- | --- |
| `Nonadditivity.Haar` | 167 | 890.13 | 890.04 | -0.09 | 0.26 |
| `Audit` | 1 | 261.64 | 261.05 | -0.59 | -0.58 |
| `Nonadditivity.Regular` | 6 | 268.46 | 259.45 | -9.01 | -8.12 |
| `Nonadditivity.Collins` | 4 | 124.53 | 125.36 | 0.83 | 0.42 |
| `Nonadditivity.Universal` | 5 | 116.51 | 118.72 | 2.21 | 0.29 |
| `Nonadditivity.Net` | 3 | 116.52 | 115.25 | -1.27 | -0.32 |
| `Nonadditivity.Product` | 9 | 111.87 | 112.44 | 0.57 | -0.14 |
| `Nonadditivity.Noncommutative` | 11 | 110.20 | 109.96 | -0.24 | -0.55 |
| `Nonadditivity.Quantum` | 22 | 102.96 | 103.63 | 0.67 | 0.11 |
| `Nonadditivity.Structured` | 6 | 78.66 | 78.64 | -0.02 | 0.18 |
| `Nonadditivity.Initial` | 1 | 76.07 | 76.36 | 0.29 | 0.08 |
| `Nonadditivity.Gaussian` | 11 | 74.37 | 74.22 | -0.15 | -0.14 |
| `Nonadditivity.Finite` | 7 | 68.41 | 67.70 | -0.71 | -0.15 |
| `Nonadditivity.Operational` | 15 | 61.91 | 62.48 | 0.57 | 0.39 |
| `Nonadditivity.Free` | 5 | 43.06 | 42.91 | -0.15 | -0.17 |
| `Nonadditivity.Weyl` | 8 | 41.00 | 41.40 | 0.40 | 0.24 |
| `Nonadditivity.Prescribed` | 7 | 40.99 | 40.92 | -0.07 | 0.04 |
| `Nonadditivity.Quantitative` | 2 | 40.28 | 40.37 | 0.09 | -0.04 |
| `Nonadditivity.Weighted` | 8 | 33.02 | 32.71 | -0.31 | -0.20 |
| `Nonadditivity.Positive` | 2 | 29.20 | 28.66 | -0.54 | -0.01 |
| `Nonadditivity.Entropy` | 5 | 28.58 | 28.31 | -0.27 | -0.18 |
| `Nonadditivity.Damped` | 4 | 28.23 | 28.16 | -0.07 | 0.15 |
| `Nonadditivity.Matrix` | 3 | 24.06 | 24.03 | -0.03 | -0.06 |
| `Nonadditivity.Channel` | 4 | 18.08 | 18.07 | -0.01 | -0.16 |
| `Nonadditivity.Polynomial` | 2 | 18.02 | 17.87 | -0.15 | -0.02 |
| `Nonadditivity.Linearization` | 1 | 17.86 | 17.77 | -0.09 | -0.06 |
| `Nonadditivity.Holevo` | 5 | 17.08 | 17.18 | 0.10 | 0.07 |
| `Nonadditivity.Shift` | 1 | 17.02 | 16.78 | -0.24 | -0.12 |
| `Nonadditivity.Word` | 1 | 14.88 | 14.62 | -0.26 | -0.05 |
| `Nonadditivity.Tensor` | 2 | 12.70 | 12.85 | 0.15 | 0.03 |
| `Nonadditivity.Block` | 3 | 11.13 | 11.12 | -0.01 | -0.06 |
| `Nonadditivity.General` | 1 | 9.57 | 9.79 | 0.22 | 0.11 |
| `Nonadditivity.Spectral` | 1 | 9.41 | 9.65 | 0.24 | 0.11 |
| `Nonadditivity.Upper` | 1 | 8.88 | 9.04 | 0.16 | 0.11 |
| `Nonadditivity.Channels` | 1 | 9.13 | 8.95 | -0.18 | -0.11 |
| `Nonadditivity.Asymptotics` | 1 | 8.67 | 8.62 | -0.05 | 0.03 |
| `Nonadditivity.Observable` | 1 | 8.46 | 8.19 | -0.27 | -0.13 |
| `Nonadditivity.Deterministic` | 2 | 8.09 | 8.08 | -0.01 | -0.02 |
| `Nonadditivity.Quadratic` | 1 | 6.69 | 6.61 | -0.08 | -0.07 |
| `Nonadditivity.Bell` | 1 | 6.59 | 6.50 | -0.09 | -0.03 |
| `Nonadditivity.Probability` | 2 | 5.46 | 5.49 | 0.03 | 0.02 |
| `Nonadditivity.Adjoint` | 1 | 5.40 | 5.35 | -0.05 | -0.06 |
| `Nonadditivity.Short` | 1 | 5.08 | 5.05 | -0.03 | -0.01 |
| `Nonadditivity.Complementary` | 1 | 4.96 | 5.02 | 0.06 | -0.02 |
| `Nonadditivity.Scalar` | 1 | 4.70 | 4.73 | 0.03 | 0.04 |
| `Nonadditivity.Exact` | 1 | 4.53 | 4.51 | -0.02 | -0.02 |
| `Nonadditivity.Conversion` | 1 | 4.39 | 4.50 | 0.11 | 0.07 |
| `Nonadditivity.Complex` | 1 | 4.32 | 4.41 | 0.09 | 0.06 |
| `Nonadditivity.One` | 1 | 4.41 | 4.41 | 0.00 | -0.02 |
| `Nonadditivity.Small` | 1 | 4.32 | 4.34 | 0.02 | 0.03 |
| `Nonadditivity.Actual` | 1 | 4.31 | 4.33 | 0.02 | -0.04 |
| `Nonadditivity.Regularized` | 1 | 3.99 | 4.03 | 0.04 | 0.02 |
| `Nonadditivity.Canonical` | 1 | 3.93 | 3.97 | 0.04 | 0.02 |
| `Nonadditivity.State` | 1 | 3.88 | 3.75 | -0.13 | -0.14 |
| `Nonadditivity.Strict` | 1 | 3.67 | 3.63 | -0.04 | -0.02 |
| `Nonadditivity.Pure` | 1 | 3.58 | 3.54 | -0.04 | -0.02 |
| `Nonadditivity.Qualitative` | 1 | 3.30 | 3.32 | 0.02 | 0.01 |
| `Nonadditivity.Main` | 1 | 3.30 | 3.27 | -0.03 | -0.01 |
| `Nonadditivity.Purity` | 1 | 3.22 | 3.20 | -0.02 | -0.01 |
| `Nonadditivity.Damping` | 1 | 3.20 | 3.19 | -0.01 | -0.02 |
| `Nonadditivity.Gap` | 1 | 3.10 | 3.11 | 0.01 | 0.01 |
| `Nonadditivity.Switch` | 1 | 2.95 | 2.97 | 0.02 | 0.03 |
| `Nonadditivity` | 1 | 2.74 | 2.83 | 0.09 | 0.10 |
| `All` | 1 | 2.75 | 2.81 | 0.06 | 0.05 |
| `Nonadditivity.Dimensions` | 1 | 2.78 | 2.78 | 0.00 | -0.03 |
| `Nonadditivity.Conjugate` | 1 | 2.68 | 2.67 | -0.01 | -0.02 |
| `Nonadditivity.Conditional` | 1 | 2.62 | 2.64 | 0.02 | 0.01 |

These are reproducible filename families in the flat module directory, not parsed Lean namespaces.

## Committed-source census

| Metric | Before | After |
| --- | --- | --- |
| maximum_physical_lines | 728 | 728 |
| legacy_nonmodule_count | 369 | 369 |
| files over 1000 physical lines | 0 | 0 |
| files over 1500 physical lines | 0 | 0 |

| Override | Before occurrences | After occurrences |
| --- | --- | --- |
| maxHeartbeats | 125 | 125 |
| synthInstance.maxHeartbeats | 3 | 3 |
| maxRecDepth | 1 | 1 |

| Tactic token | Before | After |
| --- | --- | --- |
| nlinarith | 219 | 219 |
| linarith | 416 | 416 |
| simp | 2809 | 2809 |
| simpa | 913 | 913 |
| congr | 176 | 176 |
| norm_num | 332 | 332 |
| positivity | 466 | 466 |
| omega | 578 | 578 |
| aesop | 0 | 0 |

Lexical tactic tokens and set_option occurrences, excluding comments/strings; not executed tactic counts or option lifetime analysis. Legacy module headers are recorded; this pass does not migrate module syntax. Full per-file override locations and large-file lists are retained in JSON.

## Cached dependency provenance

| Snapshot | Package | Cached oleans | Resolved cache path |
| --- | --- | --- | --- |
| Before | LeanSearchClient | 4 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/LeanSearchClient` |
| Before | Qq | 14 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/Qq` |
| Before | aesop | 135 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/aesop` |
| Before | batteries | 174 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/batteries` |
| Before | importGraph | 10 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/importGraph` |
| Before | mathlib | 7805 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/mathlib` |
| Before | plausible | 11 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/plausible` |
| Before | proofwidgets | 12 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/proofwidgets` |
| After | LeanSearchClient | 4 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/LeanSearchClient` |
| After | Qq | 14 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/Qq` |
| After | aesop | 135 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/aesop` |
| After | batteries | 174 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/batteries` |
| After | importGraph | 10 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/importGraph` |
| After | mathlib | 7805 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/mathlib` |
| After | plausible | 11 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/plausible` |
| After | proofwidgets | 12 | `/home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/.lake/packages/proofwidgets` |

Every required direct external import resolved before measurement. Initial/final cached-package artifact size, mtime and inode manifests agree within each run; dependencies were inputs, not compilation targets. This cannot detect a mutation perfectly restored between snapshots. Lean standard-library paths are resolved by the pinned toolchain; package stat manifests do not additionally inventory all standard-library artifacts.

## Matched warm own-file profiles

Serial, warm, own-file profiles omit olean output. Exclusive profiler phases are not a complete wall-time partition. Missing categories are not substituted with zero; unmatched modules do not establish phase changes.

| Module | After profile provenance | Exclusive phase | Before s | After s | Delta s |
| --- | --- | --- | --- | --- | --- |
| `Audit` | full after snapshot | attribute application | 0.000 | 0.000 | -0.000 |
| `Audit` | full after snapshot | blocked (unaccounted) | 0.047 | 0.050 | 0.003 |
| `Audit` | full after snapshot | compilation (IR) | 0.001 | 0.001 | 0.000 |
| `Audit` | full after snapshot | compilation (LCNF base) | 0.025 | 0.025 | 0.000 |
| `Audit` | full after snapshot | compilation (LCNF impure) | 0.002 | 0.003 | 0.000 |
| `Audit` | full after snapshot | compilation (LCNF mono) | 0.009 | 0.009 | 0.000 |
| `Audit` | full after snapshot | elaboration | 251.000 | 253.000 | 2.000 |
| `Audit` | full after snapshot | fix level params | 0.000 | 0.000 | 0.000 |
| `Audit` | full after snapshot | import | 2.360 | 2.320 | -0.040 |
| `Audit` | full after snapshot | initialization | 0.033 | 0.041 | 0.008 |
| `Audit` | full after snapshot | instantiate metavars | 0.000 | 0.000 | -0.000 |
| `Audit` | full after snapshot | interpretation | 5.570 | 5.580 | 0.010 |
| `Audit` | full after snapshot | let-to-have transformation | 0.000 | 0.000 | -0.000 |
| `Audit` | full after snapshot | linting | 0.020 | 0.019 | -0.001 |
| `Audit` | full after snapshot | parsing | 0.014 | 0.013 | -0.001 |
| `Audit` | full after snapshot | process pre-definitions | 0.001 | 0.001 | 0.000 |
| `Audit` | full after snapshot | share common exprs | 0.000 | 0.000 | 0.000 |
| `Audit` | full after snapshot | type checking | 0.002 | 0.002 | 0.001 |
| `Audit` | full after snapshot | typeclass inference | 0.017 | 0.017 | 0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | attribute application | 0.019 | 0.019 | -0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | blocked (unaccounted) | — | 0.000 | — |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | compilation (IR) | 0.001 | 0.001 | 0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | compilation (LCNF base) | 0.004 | 0.004 | 0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | compilation (LCNF impure) | 0.001 | 0.001 | -0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | compilation (LCNF mono) | 0.005 | 0.005 | -0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | congr simp thm | 0.054 | 0.054 | 0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | dsimp | 0.002 | 0.003 | 0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | elaboration | 1.660 | 1.670 | 0.010 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | fix level params | 0.020 | 0.022 | 0.002 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | import | 1.990 | 2.000 | 0.010 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | initialization | 0.034 | 0.035 | 0.001 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | instantiate metavars | 0.050 | 0.046 | -0.004 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | interpretation | 1.640 | 1.600 | -0.040 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | let-to-have transformation | 0.010 | 0.009 | -0.001 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | linting | 0.074 | 0.073 | -0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | norm_num | 0.010 | 0.009 | -0.000 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | parsing | 0.049 | 0.048 | -0.001 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | process pre-definitions | 0.086 | 0.086 | -0.001 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | ring | 0.068 | 0.068 | 0.001 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | share common exprs | 0.083 | 0.079 | -0.005 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | simp | 6.730 | 6.830 | 0.100 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | tactic execution | 7.750 | 7.690 | -0.060 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | type checking | 1.560 | 1.500 | -0.060 |
| `Nonadditivity.CollinsYounTensor` | full after snapshot | typeclass inference | 45.200 | 45.600 | 0.400 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | attribute application | 0.019 | 0.019 | -0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | compilation (IR) | 0.001 | 0.001 | -0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | compilation (LCNF base) | 0.006 | 0.005 | -0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | compilation (LCNF impure) | 0.002 | 0.002 | -0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | compilation (LCNF mono) | 0.007 | 0.006 | -0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | congr simp thm | 0.065 | 0.072 | 0.007 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | elaboration | 1.590 | 1.620 | 0.030 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | fix level params | 0.011 | 0.012 | 0.001 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | import | 2.150 | 2.150 | 0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | initialization | 0.034 | 0.035 | 0.002 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | instantiate metavars | 0.041 | 0.042 | 0.001 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | interpretation | 1.460 | 1.430 | -0.030 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | let-to-have transformation | 0.004 | 0.004 | 0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | linting | 0.093 | 0.098 | 0.006 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | norm_num | 0.042 | 0.041 | -0.001 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | parsing | 0.059 | 0.061 | 0.002 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | process pre-definitions | 0.106 | 0.110 | 0.004 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | ring | 0.033 | 0.033 | 0.000 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | share common exprs | 0.077 | 0.080 | 0.002 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | simp | 6.340 | 6.250 | -0.090 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | tactic execution | 22.000 | 23.400 | 1.400 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | type checking | 2.040 | 1.930 | -0.110 |
| `Nonadditivity.InitialNetReduction` | full after snapshot | typeclass inference | 34.700 | 33.800 | -0.900 |
| `Nonadditivity.NetPolynomial` | full after snapshot | attribute application | 0.021 | 0.020 | -0.001 |
| `Nonadditivity.NetPolynomial` | full after snapshot | compilation (IR) | 0.001 | 0.001 | -0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | compilation (LCNF base) | 0.011 | 0.011 | 0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | compilation (LCNF impure) | 0.001 | 0.001 | -0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | compilation (LCNF mono) | 0.005 | 0.005 | -0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | congr simp thm | 0.023 | 0.024 | 0.002 |
| `Nonadditivity.NetPolynomial` | full after snapshot | elaboration | 0.977 | 1.050 | 0.073 |
| `Nonadditivity.NetPolynomial` | full after snapshot | fix level params | 0.013 | 0.013 | 0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | import | 2.150 | 2.150 | 0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | initialization | 0.034 | 0.041 | 0.007 |
| `Nonadditivity.NetPolynomial` | full after snapshot | instantiate metavars | 0.031 | 0.033 | 0.002 |
| `Nonadditivity.NetPolynomial` | full after snapshot | interpretation | 0.818 | 0.822 | 0.004 |
| `Nonadditivity.NetPolynomial` | full after snapshot | let-to-have transformation | 0.005 | 0.005 | 0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | linting | 0.066 | 0.069 | 0.003 |
| `Nonadditivity.NetPolynomial` | full after snapshot | norm_num | 0.004 | 0.004 | 0.000 |
| `Nonadditivity.NetPolynomial` | full after snapshot | parsing | 0.046 | 0.047 | 0.001 |
| `Nonadditivity.NetPolynomial` | full after snapshot | process pre-definitions | 0.076 | 0.087 | 0.011 |
| `Nonadditivity.NetPolynomial` | full after snapshot | share common exprs | 0.051 | 0.054 | 0.002 |
| `Nonadditivity.NetPolynomial` | full after snapshot | simp | 6.660 | 6.830 | 0.170 |
| `Nonadditivity.NetPolynomial` | full after snapshot | tactic execution | 25.300 | 24.900 | -0.400 |
| `Nonadditivity.NetPolynomial` | full after snapshot | type checking | 2.660 | 2.740 | 0.080 |
| `Nonadditivity.NetPolynomial` | full after snapshot | typeclass inference | 29.900 | 29.600 | -0.300 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | attribute application | 0.000 | 0.000 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | blocked (unaccounted) | 0.934 | 0.940 | 0.006 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | compilation (IR) | 0.001 | 0.001 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | compilation (LCNF base) | 0.019 | 0.019 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | compilation (LCNF impure) | 0.003 | 0.003 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | compilation (LCNF mono) | 0.010 | 0.010 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | congr simp thm | 0.036 | 0.042 | 0.007 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | elaboration | 0.290 | 0.312 | 0.022 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | fix level params | 0.003 | 0.004 | 0.001 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | import | 1.880 | 1.900 | 0.020 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | initialization | 0.034 | 0.032 | -0.002 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | instantiate metavars | 0.008 | 0.008 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | interpretation | 0.373 | 0.372 | -0.001 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | let-to-have transformation | 0.000 | 0.001 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | linting | 0.029 | 0.027 | -0.001 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | parsing | 0.015 | 0.019 | 0.003 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | process pre-definitions | 0.059 | 0.055 | -0.004 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | share common exprs | 0.008 | 0.008 | 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | simp | 6.050 | 6.160 | 0.110 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | tactic execution | 1.520 | 1.710 | 0.190 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | type checking | 0.334 | 0.323 | -0.011 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | full after snapshot | typeclass inference | 10.900 | 11.100 | 0.200 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | attribute application | 0.009 | 0.007 | -0.001 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | blocked (unaccounted) | 0.000 | — | — |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | compilation (IR) | 0.000 | 0.000 | 0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | compilation (LCNF base) | 0.009 | 0.008 | -0.002 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | compilation (LCNF impure) | 0.001 | 0.001 | 0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | compilation (LCNF mono) | 0.005 | 0.004 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | congr simp thm | 0.009 | 0.009 | 0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | elaboration | 0.381 | 0.375 | -0.006 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | fix level params | 0.005 | 0.005 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | import | 1.960 | 2.020 | 0.060 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | initialization | 0.032 | 0.037 | 0.005 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | instantiate metavars | 0.006 | 0.005 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | interpretation | 0.440 | 0.447 | 0.007 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | let-to-have transformation | 0.001 | 0.001 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | linting | 0.017 | 0.017 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | norm_num | 0.009 | 0.010 | 0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | parsing | 0.018 | 0.018 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | process pre-definitions | 0.044 | 0.041 | -0.003 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | share common exprs | 0.015 | 0.015 | -0.000 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | simp | 0.427 | 0.433 | 0.006 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | tactic execution | 9.290 | 1.200 | -8.090 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | type checking | 0.656 | 0.674 | 0.018 |
| `Nonadditivity.RegularCoefficientEnergy` | supplemental after warm profile | typeclass inference | 8.510 | 8.500 | -0.010 |
| `Nonadditivity.RegularFactorization` | full after snapshot | attribute application | 0.033 | 0.034 | 0.002 |
| `Nonadditivity.RegularFactorization` | full after snapshot | compilation (IR) | 0.000 | 0.000 | 0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | compilation (LCNF base) | 0.002 | 0.003 | 0.001 |
| `Nonadditivity.RegularFactorization` | full after snapshot | compilation (LCNF impure) | 0.000 | 0.000 | 0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | compilation (LCNF mono) | 0.001 | 0.001 | 0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | congr simp thm | 0.052 | 0.051 | -0.001 |
| `Nonadditivity.RegularFactorization` | full after snapshot | elaboration | 7.140 | 7.310 | 0.170 |
| `Nonadditivity.RegularFactorization` | full after snapshot | fix level params | 0.029 | 0.030 | 0.001 |
| `Nonadditivity.RegularFactorization` | full after snapshot | import | 2.000 | 2.000 | 0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | initialization | 0.035 | 0.034 | -0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | instantiate metavars | 0.032 | 0.034 | 0.002 |
| `Nonadditivity.RegularFactorization` | full after snapshot | interpretation | 1.740 | 1.700 | -0.040 |
| `Nonadditivity.RegularFactorization` | full after snapshot | let-to-have transformation | 0.006 | 0.006 | -0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | linting | 0.095 | 0.093 | -0.001 |
| `Nonadditivity.RegularFactorization` | full after snapshot | norm_num | 0.011 | 0.011 | 0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | parsing | 0.052 | 0.054 | 0.002 |
| `Nonadditivity.RegularFactorization` | full after snapshot | process pre-definitions | 0.142 | 0.141 | -0.001 |
| `Nonadditivity.RegularFactorization` | full after snapshot | ring | 0.040 | 0.040 | -0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | share common exprs | 0.120 | 0.122 | 0.002 |
| `Nonadditivity.RegularFactorization` | full after snapshot | simp | 8.370 | 8.720 | 0.350 |
| `Nonadditivity.RegularFactorization` | full after snapshot | tactic execution | 38.800 | 38.800 | 0.000 |
| `Nonadditivity.RegularFactorization` | full after snapshot | type checking | 17.800 | 18.000 | 0.200 |
| `Nonadditivity.RegularFactorization` | full after snapshot | typeclass inference | 69.700 | 70.000 | 0.300 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | attribute application | 0.005 | 0.005 | -0.000 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | congr simp thm | 0.027 | 0.028 | 0.000 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | elaboration | 1.020 | 1.030 | 0.010 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | fix level params | 0.014 | 0.015 | 0.001 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | import | 1.980 | 2.010 | 0.030 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | initialization | 0.031 | 0.034 | 0.003 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | instantiate metavars | 0.015 | 0.015 | -0.001 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | interpretation | 0.550 | 0.535 | -0.015 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | let-to-have transformation | 0.003 | 0.003 | 0.000 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | linting | 0.048 | 0.046 | -0.002 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | norm_num | 0.002 | 0.002 | 0.000 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | parsing | 0.023 | 0.022 | -0.001 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | process pre-definitions | 0.051 | 0.054 | 0.003 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | ring | 0.004 | 0.004 | -0.000 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | share common exprs | 0.051 | 0.053 | 0.002 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | simp | 0.685 | 0.700 | 0.015 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | tactic execution | 7.780 | 7.700 | -0.080 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | type checking | 19.300 | 19.600 | 0.300 |
| `Nonadditivity.UniversalFactorizationGram` | full after snapshot | typeclass inference | 23.800 | 24.000 | 0.200 |
| `Nonadditivity.UniversalFactorizationPolynomialDilation` | full after snapshot | UNMATCHED (after only) | — | — | — |

Additional profiles used only in comparison; original after summary and its independently selected top8 are unchanged. Its summary and available adjacent raw records/logs have separate SHA-256 bindings in the accompanying JSON.

### Largest retained events above 100 ms

| Side | Provenance | Module | Category | Declaration/context | Seconds |
| --- | --- | --- | --- | --- | --- |
| before | full before snapshot | `Audit` | interpretation | _private.Audit.0._eval._boxed | 5.020 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.410 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.230 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.230 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.200 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.200 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.190 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.190 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.180 |
| before | full before snapshot | `Audit` | elaboration | unattributed | 3.170 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | simp | unattributed | 2.200 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | import | unattributed | 1.990 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | simp | unattributed | 1.460 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.220 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.120 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | simp | unattributed | 0.796 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.715 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.592 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.523 |
| before | full before snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.exact | 0.489 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 8.110 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 4.370 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | import | unattributed | 2.150 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | simp | unattributed | 1.720 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.exact | 1.270 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.260 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | simp | unattributed | 1.240 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.953 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.920 |
| before | full before snapshot | `Nonadditivity.InitialNetReduction` | elaboration | unattributed | 0.654 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rcases | 7.920 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | simp | unattributed | 4.160 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.obtain | 3.610 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.obtain | 3.540 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 2.210 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | import | unattributed | 2.150 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.990 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.990 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | simp | unattributed | 1.720 |
| before | full before snapshot | `Nonadditivity.NetPolynomial` | typeclass inference | Nontrivial | 0.784 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | import | unattributed | 1.880 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | tactic execution | Lean.Parser.Tactic.simpAll | 0.453 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.363 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.265 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | tactic execution | Lean.Parser.Tactic.simpa | 0.243 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | tactic execution | Lean.Parser.Tactic.simpAll | 0.214 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.210 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.209 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.204 |
| before | full before snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.204 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | tactic execution | Lean.Parser.Tactic.exact | 8.120 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | import | unattributed | 1.960 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.444 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.361 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | StarHomClass | 0.301 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | MulActionHomClass | 0.300 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.275 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | MulHomClass | 0.209 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | AddMonoidHomClass | 0.191 |
| before | full before snapshot | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | AddMonoidHomClass | 0.183 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | type checking | unattributed | 10.900 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 5.310 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.exact | 4.610 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | simp | unattributed | 3.580 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 3.220 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 3.140 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 2.550 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | import | unattributed | 2.000 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | type checking | unattributed | 1.750 |
| before | full before snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.refine | 1.430 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | type checking | unattributed | 17.800 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | import | unattributed | 1.980 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | Module | 1.460 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.898 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.773 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.741 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.737 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.604 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.573 |
| before | full before snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.567 |
| after | full after snapshot | `Audit` | interpretation | _private.Audit.0._eval._boxed | 5.060 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.290 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.280 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.270 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.230 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.200 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.200 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.190 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.190 |
| after | full after snapshot | `Audit` | elaboration | unattributed | 3.190 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | simp | unattributed | 2.230 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | import | unattributed | 2.000 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | simp | unattributed | 1.480 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.200 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.110 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | simp | unattributed | 0.806 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.exact | 0.627 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.589 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.583 |
| after | full after snapshot | `Nonadditivity.CollinsYounTensor` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.555 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 9.850 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 4.200 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | import | unattributed | 2.150 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | simp | unattributed | 1.780 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.260 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | simp | unattributed | 1.160 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.exact | 1.150 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.895 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.848 |
| after | full after snapshot | `Nonadditivity.InitialNetReduction` | elaboration | unattributed | 0.665 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rcases | 8.050 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | simp | unattributed | 4.290 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.obtain | 3.540 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.obtain | 3.510 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | import | unattributed | 2.150 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 2.140 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.990 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 1.960 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | simp | unattributed | 1.650 |
| after | full after snapshot | `Nonadditivity.NetPolynomial` | typeclass inference | Nontrivial | 0.903 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | import | unattributed | 1.900 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | tactic execution | Lean.Parser.Tactic.simpAll | 0.531 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.380 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | tactic execution | Lean.Parser.Tactic.simpa | 0.279 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.258 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | tactic execution | Lean.Parser.Tactic.simpAll | 0.245 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.216 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.213 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.208 |
| after | full after snapshot | `Nonadditivity.NoncommutativeCSSkeletonDecoration` | simp | unattributed | 0.201 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | import | unattributed | 2.020 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.445 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.358 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | StarHomClass | 0.312 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | MulActionHomClass | 0.301 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.274 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | MulHomClass | 0.197 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | AddMonoidHomClass | 0.195 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | AddMonoidHomClass | 0.184 |
| after | supplemental after warm profile | `Nonadditivity.RegularCoefficientEnergy` | typeclass inference | SeminormedAddGroup | 0.149 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | type checking | unattributed | 11.000 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 5.450 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.exact | 4.860 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | simp | unattributed | 3.780 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 3.140 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 2.950 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 2.460 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | import | unattributed | 2.000 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | type checking | unattributed | 1.780 |
| after | full after snapshot | `Nonadditivity.RegularFactorization` | elaboration | unattributed | 1.330 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | type checking | unattributed | 18.000 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | import | unattributed | 2.010 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | Module | 1.690 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.907 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.754 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.748 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.712 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.581 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.494 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationGram` | typeclass inference | NonUnitalContinuousFunctionalCalculus | 0.487 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | DistribMulAction | 2.860 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | import | unattributed | 1.990 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | AddHomClass | 1.250 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | MulActionHomClass | 0.872 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | StarHomClass | 0.860 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | Algebra | 0.413 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | AddMonoidHomClass | 0.342 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | Module | 0.295 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | typeclass inference | Module | 0.291 |
| after | full after snapshot | `Nonadditivity.UniversalFactorizationPolynomialDilation` | tactic execution | Lean.Parser.Tactic.rewriteSeq | 0.209 |

At most ten events per module and side appear here; full events remain in the measured JSON/raw logs. An anonymous elaboration event needs declaration tracing and statement/proof isolation before a proof-level cause is claimed.

## Interventions and A/B evidence

| Module | Intervention | Classification | Basis | Runs B/A | Median before s | Median after s | Saving s / % | Threshold + evidence requirements | Reported kept |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Nonadditivity.RegularCoefficientEnergy` | Give Equiv.summable_iff its explicit norm-power summand | valid completed A/B | phase: tactic execution | 3/3 | 9.24 | 1.14 | 8.10 / 87.66 | supported | True |
| `Nonadditivity.NetPolynomial` | Give the spectral endpoint theorem explicit algebra and element arguments | valid completed A/B | phase: tactic execution | 3/3 | 25.60 | 25.20 | 0.40 / 1.56 | not established | False |
| `Nonadditivity.UniversalFactorizationGram` | Extract the operator sandwich into a generic private helper | FAILED; performance comparison excluded | phase: type checking | 3/3 | — | — | — / — | excluded failed attempt | False |

Failed intervention in `Nonadditivity.UniversalFactorizationGram`: All three candidate runs hit deterministic whnf/tactic-execution timeouts at the unchanged 1,000,000-heartbeat limit (UniversalFactorizationGram lines78/81); all three baseline controls passed.
Valid baseline control attempts and failed candidate attempts were retained. Candidate medians and savings are excluded; this is neither a valid speed regression nor a valid null result.

| Candidate attempt | Compiler exit | Wall s (diagnostic) | CPU s (diagnostic) | Errors |
| --- | --- | --- | --- | --- |
| 1 | 1 | 96.09 | 148.48 | (deterministic) timeout at `whnf`, maximum number of heartbeats (1000000) has been reached; (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (1000000) has been reached |
| 2 | 1 | 95.78 | 148.95 | (deterministic) timeout at `whnf`, maximum number of heartbeats (1000000) has been reached; (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (1000000) has been reached |
| 3 | 1 | 95.27 | 147.52 | (deterministic) timeout at `whnf`, maximum number of heartbeats (1000000) has been reached; (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (1000000) has been reached |

A retained performance intervention requires a ≥2 second or ≥10% improvement in its relevant phase, with matching setup, unchanged statements and no transferred regression. A wall-time claim requires at least three runs on each side. Median values are used here; supplied raw evidence and reverted/null experiments must remain reviewable.

## Parallelism, contention and size prediction

Code-line change: **2**. Baseline CPU cost: **69.147 ms/code line**. Predicted CPU change from size alone: **0.14 s**. Actual summed own CPU change: **-8.18 s**. Absolute actual/predicted ratio: **59.15** (undefined when predicted change is zero).

| Conservative contention screen | Observed |
| --- | --- |
| outer_user_cpu_down_while_summed_module_wall_up | False |
| observed_cpu_parallelism_increased_over_10_percent | False |
| matched_modules_with_opposite_wall_cpu_changes_over_10_percent | False |

Conservative screening heuristics adapted to actual GNU CPU and module wall measurements. Signals do not prove contention; their absence does not prove a quiet machine. Process invisibility is not a zero-load observation.
Multiple screening signals are present: **False**. Single whole-build runs still admit cache, scheduler, thermal and background-load noise; causality rests on targeted A/B evidence.

The driver is serial. Host-core work floors and weighted import chains in the original snapshots are hypothetical scheduling bounds; they do not describe this serial driver's observed schedule.

## Public theorem/API preservation

A supplied, source-bound record reports a **passed** comparison of **5323** public declarations and all **6** challenge roots, using independently decoded canonical kernel-type bytes and exact public inventory/identity fields.

Type identity does not prove unchanged definition bodies or English-to-Lean equivalence.

## Reproduction and evidence

```sh
/opt/homebrew/opt/python@3.13/bin/python3.13 /Users/jw/.codex/.chatgpt-projects/g-p-6ab2299d76c081919816db08eadec5a3/nonadditivity-release/scripts/compare_elaboration.py --repo . --before verification/elaboration-20261006/before/summary.json --after verification/elaboration-20261006/after/summary.json --after-supplemental-profiles verification/elaboration-20261006/matched-profiles/summary.json --dead-code-json verification/elaboration-20261006/dead-code.json --api-check verification/elaboration-20261006/public-types.json --ab-summary verification/elaboration-20261006/ab/trial-1.json --ab-summary verification/elaboration-20261006/ab/trial-2.json --ab-summary verification/elaboration-20261006/ab/trial-3.json --output verification/elaboration-20261006/comparison
```

This generator runs no compiler or proof checker. Reproduce the measurements using each snapshot's recorded harness invocation; keep cached dependencies populated and preserve the same compiler, GNU time and serial scheduling. Source censuses come from the snapshot commits and recorded build-scope inventories, never a moving working tree.

Before harness invocation:

```sh
/opt/hostedtoolcache/Python/3.11.17/x64/bin/python /home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/scripts/elaboration_test.py --label before --output /home/runner/work/_temp/elaboration-evidence/before --time-bin /usr/bin/time
```

After harness invocation:

```sh
/opt/hostedtoolcache/Python/3.11.17/x64/bin/python /home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/scripts/elaboration_test.py --label after --output /home/runner/work/_temp/elaboration-evidence/after --time-bin /usr/bin/time --prior-summary /home/runner/work/_temp/elaboration-evidence/before/summary.json
```

Inputs and their SHA-256 bindings, all joined module deltas, full source censuses and evidence paths are in `comparison.json`. Original before/after reports and raw logs remain the authoritative measured observations. Two snapshots cannot establish a monotonic trend.
