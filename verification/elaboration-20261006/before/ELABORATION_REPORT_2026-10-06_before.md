# Elaboration report — 2026-10-06 (before)

## Setup and provenance

Window: 2026-10-06T22:59:47+00:00 to 2026-10-06T23:43:40+00:00.
Commit: `743cc95bc4c0b1bca891994def26d9e5f8c7aad6`. Host: `runnervmwvtoz` (Linux-6.8.0-1064-azure-x86_64-with-glibc2.35).
Pinned compiler: `/home/runner/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean`; Lean (version 4.29.0-rc6, x86_64-unknown-linux-gnu, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release).
Timing: `/usr/bin/time`; time (GNU Time) UNKNOWN.
RSS interpretation: GNU time maxrss is reported in KiB on this Linux host.

The existing `./build.sh` recompiles every own module in serial order; no cache was removed.
Dependency oleans are inputs. Their initial/final stat manifests are retained separately.
Initial co-running Lean/Lake processes: 0; final: 0. Presence or unavailable process visibility alone does not invalidate this run.

## Size snapshot

| Scope | Lean files | Counted files | Physical lines | Non-comment code lines | Comment-only excluded |
| --- | ---: | ---: | ---: | ---: | ---: |
| Git commit tree | 768 | 768 | 115995 | 89728 | 0 |
| Git tree own build scope | 369 | 369 | 57473 | 44492 | 0 |
| Measured working own scope | 369 | 369 | 57473 | 44492 | 0 |

The full git tree includes mirrors, comparator challenges and verification probes that the production build does not compile. Cost per line uses the measured own scope.
Legacy own files without a `module` header: 369. They are recorded in JSON; this measurement does not migrate module syntax.
Dirty status at start: `(clean)`.

## Headline

| Metric | This run | Prior run |
| --- | ---: | ---: |
| Build wall seconds | 2168.55 | — |
| User CPU seconds | 2736.76 | — |
| System CPU seconds | 405.36 | — |
| CPU percent | 144.0 | — |
| Peak RSS (raw GNU field) | 4531316 | — |
| Measured jobs | 369/369 | — |
| Cumulative own-file CPU seconds | 3076.489999999999 | — |
| CPU milliseconds per own code line | 69.1470376696934 | — |
| Own CPU / full build wall | 1.4186852966267776 | — |

Every own compiler invocation is timed, including jobs under one second. Module CPU is GNU user + system time, not a Lake progress-line estimate.

## Build health

Validity: **valid**. Build exit: 0.
Errors: 0; warnings: 104; sorry warnings: 0.
Authorized sorry modules: none.
Unauthorized static sorry/admit tokens: 0.
Coverage: `{"complete": true, "duplicates": [], "expected": 369, "failed": [], "measured": 369, "missing": [], "order_matches": true, "unexpected": []}`.
Warning census: `{"Try `simp at hi` instead of `simpa using hi`": 1, "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice": 19, "deprecated declaration/syntax": 1, "try 'simp' instead of 'simpa'": 6, "unused variable/argument": 77}`.

## Heavy tail

| Per-module wall threshold | Files | Delta vs prior |
| --- | ---: | ---: |
| ≥10s | 23 | — |
| ≥20s | 6 | — |
| ≥30s | 5 | — |
| ≥40s | 3 | — |

| Top files | Wall seconds | CPU seconds | Delta wall vs prior |
| --- | ---: | ---: | ---: |
| `Audit` | 261.22 | 261.64 | — |
| `Nonadditivity.NetPolynomial` | 62.05 | 102.88 | — |
| `Nonadditivity.RegularFactorization` | 48.29 | 146.38 | — |
| `Nonadditivity.InitialNetReduction` | 36.37 | 76.07 | — |
| `Nonadditivity.CollinsYounTensor` | 32.31 | 67.37 | — |
| `Nonadditivity.UniversalFactorizationGram` | 26.63 | 55.55 | — |
| `Nonadditivity.RegularCoefficientEnergy` | 18.09 | 22.16 | — |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | 18.04 | 21.86 | — |
| `Nonadditivity.UniversalFactorizationPolynomialDilation` | 17.60 | 19.98 | — |
| `Nonadditivity.ProductMomentBridge` | 16.34 | 36.98 | — |
| `Nonadditivity.RegularFubini` | 16.32 | 24.04 | — |
| `Nonadditivity.RegularShiftedDilation` | 15.45 | 25.60 | — |
| `Nonadditivity.HaarOperatorPolynomial` | 14.81 | 21.36 | — |
| `Nonadditivity.FreeCreation` | 14.64 | 19.31 | — |
| `Nonadditivity.RegularDilation` | 14.49 | 34.09 | — |
| `Nonadditivity.CollinsYoun` | 14.48 | 31.69 | — |
| `Nonadditivity.ProductHaagerupWords` | 13.47 | 16.00 | — |
| `Nonadditivity.StructuredLinearization` | 12.74 | 15.73 | — |
| `Nonadditivity.StructuredCostBounds` | 12.64 | 36.25 | — |
| `Nonadditivity.HaarNonbacktracking` | 12.27 | 17.63 | — |
| `Nonadditivity.Quantitative` | 12.25 | 35.79 | — |
| `Nonadditivity.FreeModel` | 11.99 | 13.19 | — |
| `Nonadditivity.FiniteSetFactorization` | 11.47 | 21.16 | — |
| `Nonadditivity.ProductHaagerupCreation` | 9.59 | 18.02 | — |
| `Nonadditivity.HaarNonbacktrackingRenewal` | 9.38 | 17.42 | — |
| `Nonadditivity.HaarWordExpansion` | 9.37 | 20.69 | — |
| `Nonadditivity.FiniteRealization` | 9.35 | 11.35 | — |
| `Nonadditivity.UniversalShiftedDilation` | 9.34 | 19.30 | — |
| `Nonadditivity.NoncommutativeCSCrossing` | 9.25 | 9.76 | — |
| `Nonadditivity.PositiveLinearization` | 9.11 | 22.74 | — |

## Module-family cost

| File-family prefix | Files | CPU seconds | Wall seconds | Delta CPU |
| --- | ---: | ---: | ---: | ---: |
| `Nonadditivity.Haar` | 167 | 890.13 | 667.42 | — |
| `Nonadditivity.Regular` | 6 | 268.46 | 119.77 | — |
| `Audit` | 1 | 261.64 | 261.22 | — |
| `Nonadditivity.Collins` | 4 | 124.53 | 60.23 | — |
| `Nonadditivity.Net` | 3 | 116.52 | 69.91 | — |
| `Nonadditivity.Universal` | 5 | 116.51 | 67.22 | — |
| `Nonadditivity.Product` | 9 | 111.87 | 68.67 | — |
| `Nonadditivity.Noncommutative` | 11 | 110.20 | 78.58 | — |
| `Nonadditivity.Quantum` | 22 | 102.96 | 76.09 | — |
| `Nonadditivity.Structured` | 6 | 78.66 | 47.13 | — |
| `Nonadditivity.Initial` | 1 | 76.07 | 36.37 | — |
| `Nonadditivity.Gaussian` | 11 | 74.37 | 50.85 | — |
| `Nonadditivity.Finite` | 7 | 68.41 | 43.13 | — |
| `Nonadditivity.Operational` | 15 | 61.91 | 48.63 | — |
| `Nonadditivity.Free` | 5 | 43.06 | 33.71 | — |
| `Nonadditivity.Weyl` | 8 | 41.00 | 33.28 | — |
| `Nonadditivity.Prescribed` | 7 | 40.99 | 29.93 | — |
| `Nonadditivity.Quantitative` | 2 | 40.28 | 15.43 | — |
| `Nonadditivity.Weighted` | 8 | 33.02 | 26.11 | — |
| `Nonadditivity.Positive` | 2 | 29.20 | 12.83 | — |
| `Nonadditivity.Entropy` | 5 | 28.58 | 17.86 | — |
| `Nonadditivity.Damped` | 4 | 28.23 | 17.85 | — |
| `Nonadditivity.Matrix` | 3 | 24.06 | 13.98 | — |
| `Nonadditivity.Channel` | 4 | 18.08 | 13.41 | — |
| `Nonadditivity.Polynomial` | 2 | 18.02 | 11.64 | — |
| `Nonadditivity.Linearization` | 1 | 17.86 | 7.69 | — |
| `Nonadditivity.Holevo` | 5 | 17.08 | 14.61 | — |
| `Nonadditivity.Shift` | 1 | 17.02 | 7.63 | — |
| `Nonadditivity.Word` | 1 | 14.88 | 6.53 | — |
| `Nonadditivity.Tensor` | 2 | 12.70 | 7.75 | — |
| `Nonadditivity.Block` | 3 | 11.13 | 8.89 | — |
| `Nonadditivity.General` | 1 | 9.57 | 4.55 | — |
| `Nonadditivity.Spectral` | 1 | 9.41 | 4.58 | — |
| `Nonadditivity.Channels` | 1 | 9.13 | 5.59 | — |
| `Nonadditivity.Upper` | 1 | 8.88 | 4.94 | — |
| `Nonadditivity.Asymptotics` | 1 | 8.67 | 3.82 | — |
| `Nonadditivity.Observable` | 1 | 8.46 | 5.35 | — |
| `Nonadditivity.Deterministic` | 2 | 8.09 | 7.20 | — |
| `Nonadditivity.Quadratic` | 1 | 6.69 | 3.87 | — |
| `Nonadditivity.Bell` | 1 | 6.59 | 3.95 | — |
| `Nonadditivity.Probability` | 2 | 5.46 | 5.24 | — |
| `Nonadditivity.Adjoint` | 1 | 5.40 | 3.54 | — |
| `Nonadditivity.Short` | 1 | 5.08 | 4.30 | — |
| `Nonadditivity.Complementary` | 1 | 4.96 | 3.55 | — |
| `Nonadditivity.Scalar` | 1 | 4.70 | 2.75 | — |
| `Nonadditivity.Exact` | 1 | 4.53 | 4.41 | — |
| `Nonadditivity.One` | 1 | 4.41 | 3.27 | — |
| `Nonadditivity.Conversion` | 1 | 4.39 | 3.60 | — |
| `Nonadditivity.Complex` | 1 | 4.32 | 3.49 | — |
| `Nonadditivity.Small` | 1 | 4.32 | 3.14 | — |
| `Nonadditivity.Actual` | 1 | 4.31 | 3.34 | — |
| `Nonadditivity.Regularized` | 1 | 3.99 | 3.10 | — |
| `Nonadditivity.Canonical` | 1 | 3.93 | 3.17 | — |
| `Nonadditivity.State` | 1 | 3.88 | 3.22 | — |
| `Nonadditivity.Strict` | 1 | 3.67 | 3.34 | — |
| `Nonadditivity.Pure` | 1 | 3.58 | 3.01 | — |
| `Nonadditivity.Qualitative` | 1 | 3.30 | 3.06 | — |
| `Nonadditivity.Main` | 1 | 3.30 | 2.92 | — |
| `Nonadditivity.Purity` | 1 | 3.22 | 2.84 | — |
| `Nonadditivity.Damping` | 1 | 3.20 | 2.96 | — |
| `Nonadditivity.Gap` | 1 | 3.10 | 2.54 | — |
| `Nonadditivity.Switch` | 1 | 2.95 | 2.78 | — |
| `Nonadditivity.Dimensions` | 1 | 2.78 | 2.35 | — |
| `All` | 1 | 2.75 | 2.76 | — |
| `Nonadditivity` | 1 | 2.74 | 2.74 | — |
| `Nonadditivity.Conjugate` | 1 | 2.68 | 2.44 | — |
| `Nonadditivity.Conditional` | 1 | 2.62 | 2.51 | — |

## Warm own-file profiles

Profiles run one at a time after the complete build, without writing oleans.

| Module | Warm wall seconds | Dominant phase | Categorized phase seconds |
| --- | ---: | --- | --- |
| `Audit` | 259.13 | elaboration | elaboration: 251.000; interpretation: 5.570; import: 2.360; blocked (unaccounted): 0.047; initialization: 0.033; compilation (LCNF base): 0.025; linting: 0.020; typeclass inference: 0.017; parsing: 0.014; compilation (LCNF mono): 0.009; compilation (LCNF impure): 0.002; type checking: 0.002; compilation (IR): 0.001; process pre-definitions: 0.001; share common exprs: 0.000; fix level params: 0.000; let-to-have transformation: 0.000; attribute application: 0.000; instantiate metavars: 0.000 |
| `Nonadditivity.NetPolynomial` | 28.33 | typeclass inference | typeclass inference: 29.900; tactic execution: 25.300; simp: 6.660; type checking: 2.660; import: 2.150; elaboration: 0.977; interpretation: 0.818; process pre-definitions: 0.076; linting: 0.066; share common exprs: 0.051; parsing: 0.046; initialization: 0.034; instantiate metavars: 0.031; congr simp thm: 0.023; attribute application: 0.021; fix level params: 0.013; compilation (LCNF base): 0.011; compilation (LCNF mono): 0.005; let-to-have transformation: 0.005; norm_num: 0.004; compilation (LCNF impure): 0.001; compilation (IR): 0.001 |
| `Nonadditivity.RegularFactorization` | 47.19 | typeclass inference | typeclass inference: 69.700; tactic execution: 38.800; type checking: 17.800; simp: 8.370; elaboration: 7.140; import: 2.000; interpretation: 1.740; process pre-definitions: 0.142; share common exprs: 0.120; linting: 0.095; parsing: 0.052; congr simp thm: 0.052; ring: 0.040; initialization: 0.035; attribute application: 0.033; instantiate metavars: 0.032; fix level params: 0.029; norm_num: 0.011; let-to-have transformation: 0.006; compilation (LCNF base): 0.002; compilation (LCNF mono): 0.001; compilation (LCNF impure): 0.000; compilation (IR): 0.000 |
| `Nonadditivity.InitialNetReduction` | 29.13 | typeclass inference | typeclass inference: 34.700; tactic execution: 22.000; simp: 6.340; import: 2.150; type checking: 2.040; elaboration: 1.590; interpretation: 1.460; process pre-definitions: 0.106; linting: 0.093; share common exprs: 0.077; congr simp thm: 0.065; parsing: 0.059; norm_num: 0.042; instantiate metavars: 0.041; initialization: 0.034; ring: 0.033; attribute application: 0.019; fix level params: 0.011; compilation (LCNF mono): 0.007; compilation (LCNF base): 0.006; let-to-have transformation: 0.004; compilation (LCNF impure): 0.002; compilation (IR): 0.001 |
| `Nonadditivity.CollinsYounTensor` | 32.01 | typeclass inference | typeclass inference: 45.200; tactic execution: 7.750; simp: 6.730; import: 1.990; elaboration: 1.660; interpretation: 1.640; type checking: 1.560; process pre-definitions: 0.086; share common exprs: 0.083; linting: 0.074; ring: 0.068; congr simp thm: 0.054; instantiate metavars: 0.050; parsing: 0.049; initialization: 0.034; fix level params: 0.020; attribute application: 0.019; let-to-have transformation: 0.010; norm_num: 0.010; compilation (LCNF mono): 0.005; compilation (LCNF base): 0.004; dsimp: 0.002; compilation (LCNF impure): 0.001; compilation (IR): 0.001 |
| `Nonadditivity.UniversalFactorizationGram` | 25.91 | typeclass inference | typeclass inference: 23.800; type checking: 19.300; tactic execution: 7.780; import: 1.980; elaboration: 1.020; simp: 0.685; interpretation: 0.550; process pre-definitions: 0.051; share common exprs: 0.051; linting: 0.048; initialization: 0.031; congr simp thm: 0.027; parsing: 0.023; instantiate metavars: 0.015; fix level params: 0.014; attribute application: 0.005; ring: 0.004; let-to-have transformation: 0.003; norm_num: 0.002 |
| `Nonadditivity.RegularCoefficientEnergy` | 17.94 | tactic execution | tactic execution: 9.290; typeclass inference: 8.510; import: 1.960; type checking: 0.656; interpretation: 0.440; simp: 0.427; elaboration: 0.381; process pre-definitions: 0.044; initialization: 0.032; parsing: 0.018; linting: 0.017; share common exprs: 0.015; compilation (LCNF base): 0.009; norm_num: 0.009; attribute application: 0.009; congr simp thm: 0.009; instantiate metavars: 0.006; fix level params: 0.005; compilation (LCNF mono): 0.005; let-to-have transformation: 0.001; compilation (LCNF impure): 0.001; compilation (IR): 0.000; blocked (unaccounted): 0.000 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | 17.76 | typeclass inference | typeclass inference: 10.900; simp: 6.050; import: 1.880; tactic execution: 1.520; blocked (unaccounted): 0.934; interpretation: 0.373; type checking: 0.334; elaboration: 0.290; process pre-definitions: 0.059; congr simp thm: 0.036; initialization: 0.034; linting: 0.029; compilation (LCNF base): 0.019; parsing: 0.015; compilation (LCNF mono): 0.010; instantiate metavars: 0.008; share common exprs: 0.008; fix level params: 0.003; compilation (LCNF impure): 0.003; compilation (IR): 0.001; let-to-have transformation: 0.000; attribute application: 0.000 |

## Findings ranked by actionability

- `Audit`: Unattributed elaboration needs declaration tracing and statement/proof isolation before a fix.
- `Nonadditivity.RegularFactorization`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.InitialNetReduction`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.NetPolynomial`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.CollinsYounTensor`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.UniversalFactorizationGram`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.NoncommutativeCSSkeletonDecoration`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.RegularCoefficientEnergy`: Inspect the named events before selecting a measured intervention.

Host work floor (4 cores): 769.12s. CPU-weighted import chain: 928.26s. Hypothetical host scheduling is chain-bound; the measured driver itself is serial.

CPU-weighted chain: `Nonadditivity.Linearization` → `Nonadditivity.PositiveLinearization` → `Nonadditivity.RegularCoefficientEnergy` → `Nonadditivity.MatrixRegularRestriction` → `Nonadditivity.RegularDilation` → `Nonadditivity.RegularShiftedDilation` → `Nonadditivity.RegularFactorization` → `Nonadditivity.NetPolynomial` → `Nonadditivity.NetPolynomialSupport` → `Nonadditivity.InitialNetReduction` → `Nonadditivity.StructuredLinearization` → `Nonadditivity.StructuredHaarModel` → `Nonadditivity.HaarWordExpansion` → `Nonadditivity.HaarNonbacktrackingRenewal` → `Nonadditivity.HaarNonbacktrackingLastReturn` → `Nonadditivity.HaarOperatorPolynomial` → `Nonadditivity.HaarOperatorCoefficient` → `Nonadditivity.HaarProfileCoefficient` → `Nonadditivity.HaarProfilePadding` → `Nonadditivity.HaarProfileBlockCoefficients` → `Nonadditivity.HaarProfilePatternBound` → `Nonadditivity.HaarProfileAssignmentBound` → `Nonadditivity.HaarProfileCompositionBound` → `Nonadditivity.HaarSkeletonSegmentation` → `Nonadditivity.HaarDecodedCoefficientBound` → `Nonadditivity.HaarRefinedCoefficientBound` → `Nonadditivity.HaarPrescribedBound` → `Nonadditivity.HaarPrescribedConsequences` → `Nonadditivity.HaarPrescribedScaling` → `Nonadditivity.PrescribedCostScalars` → `Nonadditivity.PrescribedCostDimensions` → `Nonadditivity.PrescribedCostInformation` → `Nonadditivity.PrescribedCostScaling` → `Nonadditivity.PrescribedCostCapacity` → `Nonadditivity` → `Audit` → `All`

Wall-weighted chain: 624.24s.

Measurement only; no elaboration improvement is applied by this harness.

## What is not established

Warm phase totals need not sum to wall time: startup, serialization and other work are not all categorized. Unattributed elaboration is not a proof-tactic diagnosis. Events under Lean's profiler threshold are absent from individual listings.
Peak RSS is a maximum, not a sum across files. The full-build number includes the Python and wrapper processes. Compiler startup and wrapper/guard overhead are included in full-build wall time.
Dependency guards compare stat provenance before/after; they do not prove that a mutation was made and perfectly restored between snapshots. Own sources are stat-polled and hash-checked. Other processes are disclosed, not treated as evidence of contamination.
Two snapshots do not establish a monotonic trend. Family labels use the first CamelCase component of the flat module filename (for example Haar or Operational); they are not parsed Lean namespace declarations.

## Methodology

```sh
/opt/hostedtoolcache/Python/3.11.17/x64/bin/python /home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/scripts/elaboration_test.py --label before --output /home/runner/work/_temp/elaboration-evidence/before --time-bin /usr/bin/time
# Actual timed full-build command
/usr/bin/time -v -o /home/runner/work/_temp/elaboration-evidence/before/build.time.txt /home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/build.sh
```

Per-module raw stdout/stderr and GNU time output are in `logs/` and `timings/`; exact compiler commands are in `measurements.jsonl`. `summary.json` retains source hashes, build coverage, phase events, dependency provenance pointers and guard outcomes.

## Pointers

Prior summary: `none`.
