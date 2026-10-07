# Elaboration report — 2026-10-07 (after)

## Setup and provenance

Window: 2026-10-07T00:07:50+00:00 to 2026-10-07T00:51:41+00:00.
Commit: `e943a85f0234a573477a10871f60a2d9583fa47b`. Host: `runnervmwvtoz` (Linux-6.8.0-1064-azure-x86_64-with-glibc2.35).
Pinned compiler: `/home/runner/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean`; Lean (version 4.29.0-rc6, x86_64-unknown-linux-gnu, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release).
Timing: `/usr/bin/time`; time (GNU Time) UNKNOWN.
RSS interpretation: GNU time maxrss is reported in KiB on this Linux host.

The existing `./build.sh` recompiles every own module in serial order; no cache was removed.
Dependency oleans are inputs. Their initial/final stat manifests are retained separately.
Initial co-running Lean/Lake processes: 0; final: 0. Presence or unavailable process visibility alone does not invalidate this run.

## Size snapshot

| Scope | Lean files | Counted files | Physical lines | Non-comment code lines | Comment-only excluded |
| --- | ---: | ---: | ---: | ---: | ---: |
| Git commit tree | 768 | 768 | 115997 | 89730 | 0 |
| Git tree own build scope | 369 | 369 | 57475 | 44494 | 0 |
| Measured working own scope | 369 | 369 | 57475 | 44494 | 0 |

The full git tree includes mirrors, comparator challenges and verification probes that the production build does not compile. Cost per line uses the measured own scope.
Legacy own files without a `module` header: 369. They are recorded in JSON; this measurement does not migrate module syntax.
Dirty status at start: `(clean)`.

## Headline

| Metric | This run | Prior run |
| --- | ---: | ---: |
| Build wall seconds | 2162.44 | 2168.55 |
| User CPU seconds | 2730.2 | 2736.76 |
| System CPU seconds | 406.61 | 405.36 |
| CPU percent | 145.0 | 144.0 |
| Peak RSS (raw GNU field) | 4537440 | 4531316 |
| Measured jobs | 369/369 | — |
| Cumulative own-file CPU seconds | 3068.309999999997 | 3076.489999999999 |
| CPU milliseconds per own code line | 68.960084505776 | 69.1470376696934 |
| Own CPU / full build wall | 1.4189110449307252 | — |

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
| ≥10s | 22 | -1 |
| ≥20s | 6 | 0 |
| ≥30s | 5 | 0 |
| ≥40s | 3 | 0 |

| Top files | Wall seconds | CPU seconds | Delta wall vs prior |
| --- | ---: | ---: | ---: |
| `Audit` | 260.64 | 261.05 | -0.58 |
| `Nonadditivity.NetPolynomial` | 61.75 | 101.64 | -0.30 |
| `Nonadditivity.RegularFactorization` | 48.41 | 146.49 | +0.12 |
| `Nonadditivity.InitialNetReduction` | 36.45 | 76.36 | +0.08 |
| `Nonadditivity.CollinsYounTensor` | 32.50 | 67.97 | +0.19 |
| `Nonadditivity.UniversalFactorizationGram` | 26.42 | 56.21 | -0.21 |
| `Nonadditivity.UniversalFactorizationPolynomialDilation` | 18.01 | 20.46 | +0.41 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | 17.79 | 21.67 | -0.25 |
| `Nonadditivity.ProductMomentBridge` | 16.49 | 37.74 | +0.15 |
| `Nonadditivity.RegularFubini` | 16.08 | 23.62 | -0.24 |
| `Nonadditivity.RegularShiftedDilation` | 15.27 | 25.34 | -0.18 |
| `Nonadditivity.RegularDilation` | 15.00 | 33.52 | +0.51 |
| `Nonadditivity.FreeCreation` | 14.56 | 19.25 | -0.08 |
| `Nonadditivity.HaarOperatorPolynomial` | 14.54 | 20.99 | -0.27 |
| `Nonadditivity.CollinsYoun` | 14.40 | 31.82 | -0.08 |
| `Nonadditivity.ProductHaagerupWords` | 13.57 | 16.19 | +0.10 |
| `Nonadditivity.StructuredCostBounds` | 12.82 | 36.24 | +0.18 |
| `Nonadditivity.StructuredLinearization` | 12.63 | 15.60 | -0.11 |
| `Nonadditivity.Quantitative` | 12.30 | 35.99 | +0.05 |
| `Nonadditivity.HaarNonbacktracking` | 11.97 | 17.84 | -0.30 |
| `Nonadditivity.FreeModel` | 11.96 | 13.15 | -0.03 |
| `Nonadditivity.FiniteSetFactorization` | 11.64 | 21.11 | +0.17 |
| `Nonadditivity.RegularCoefficientEnergy` | 9.73 | 14.09 | -8.36 |
| `Nonadditivity.ProductHaagerupCreation` | 9.59 | 17.81 | +0.00 |
| `Nonadditivity.UniversalShiftedDilation` | 9.59 | 19.74 | +0.25 |
| `Nonadditivity.NoncommutativeCSCrossing` | 9.38 | 9.87 | +0.13 |
| `Nonadditivity.CollinsYounProduct` | 9.35 | 20.42 | — |
| `Nonadditivity.HaarNonbacktrackingRenewal` | 9.31 | 17.31 | -0.07 |
| `Nonadditivity.HaarWordExpansion` | 9.30 | 20.70 | -0.07 |
| `Nonadditivity.FiniteRealization` | 9.25 | 11.18 | -0.10 |

## Module-family cost

| File-family prefix | Files | CPU seconds | Wall seconds | Delta CPU |
| --- | ---: | ---: | ---: | ---: |
| `Nonadditivity.Haar` | 167 | 890.04 | 667.68 | -0.09 |
| `Audit` | 1 | 261.05 | 260.64 | -0.59 |
| `Nonadditivity.Regular` | 6 | 259.45 | 111.65 | -9.01 |
| `Nonadditivity.Collins` | 4 | 125.36 | 60.65 | +0.83 |
| `Nonadditivity.Universal` | 5 | 118.72 | 67.51 | +2.21 |
| `Nonadditivity.Net` | 3 | 115.25 | 69.59 | -1.27 |
| `Nonadditivity.Product` | 9 | 112.44 | 68.53 | +0.57 |
| `Nonadditivity.Noncommutative` | 11 | 109.96 | 78.03 | -0.24 |
| `Nonadditivity.Quantum` | 22 | 103.63 | 76.20 | +0.67 |
| `Nonadditivity.Structured` | 6 | 78.64 | 47.31 | -0.02 |
| `Nonadditivity.Initial` | 1 | 76.36 | 36.45 | +0.29 |
| `Nonadditivity.Gaussian` | 11 | 74.22 | 50.71 | -0.15 |
| `Nonadditivity.Finite` | 7 | 67.70 | 42.98 | -0.71 |
| `Nonadditivity.Operational` | 15 | 62.48 | 49.02 | +0.57 |
| `Nonadditivity.Free` | 5 | 42.91 | 33.54 | -0.15 |
| `Nonadditivity.Weyl` | 8 | 41.40 | 33.52 | +0.40 |
| `Nonadditivity.Prescribed` | 7 | 40.92 | 29.97 | -0.07 |
| `Nonadditivity.Quantitative` | 2 | 40.37 | 15.39 | +0.09 |
| `Nonadditivity.Weighted` | 8 | 32.71 | 25.91 | -0.31 |
| `Nonadditivity.Positive` | 2 | 28.66 | 12.82 | -0.54 |
| `Nonadditivity.Entropy` | 5 | 28.31 | 17.68 | -0.27 |
| `Nonadditivity.Damped` | 4 | 28.16 | 18.00 | -0.07 |
| `Nonadditivity.Matrix` | 3 | 24.03 | 13.92 | -0.03 |
| `Nonadditivity.Channel` | 4 | 18.07 | 13.25 | -0.01 |
| `Nonadditivity.Polynomial` | 2 | 17.87 | 11.62 | -0.15 |
| `Nonadditivity.Linearization` | 1 | 17.77 | 7.63 | -0.09 |
| `Nonadditivity.Holevo` | 5 | 17.18 | 14.68 | +0.10 |
| `Nonadditivity.Shift` | 1 | 16.78 | 7.51 | -0.24 |
| `Nonadditivity.Word` | 1 | 14.62 | 6.48 | -0.26 |
| `Nonadditivity.Tensor` | 2 | 12.85 | 7.78 | +0.15 |
| `Nonadditivity.Block` | 3 | 11.12 | 8.83 | -0.01 |
| `Nonadditivity.General` | 1 | 9.79 | 4.66 | +0.22 |
| `Nonadditivity.Spectral` | 1 | 9.65 | 4.69 | +0.24 |
| `Nonadditivity.Upper` | 1 | 9.04 | 5.05 | +0.16 |
| `Nonadditivity.Channels` | 1 | 8.95 | 5.48 | -0.18 |
| `Nonadditivity.Asymptotics` | 1 | 8.62 | 3.85 | -0.05 |
| `Nonadditivity.Observable` | 1 | 8.19 | 5.22 | -0.27 |
| `Nonadditivity.Deterministic` | 2 | 8.08 | 7.18 | -0.01 |
| `Nonadditivity.Quadratic` | 1 | 6.61 | 3.80 | -0.08 |
| `Nonadditivity.Bell` | 1 | 6.50 | 3.92 | -0.09 |
| `Nonadditivity.Probability` | 2 | 5.49 | 5.26 | +0.03 |
| `Nonadditivity.Adjoint` | 1 | 5.35 | 3.48 | -0.05 |
| `Nonadditivity.Short` | 1 | 5.05 | 4.29 | -0.03 |
| `Nonadditivity.Complementary` | 1 | 5.02 | 3.53 | +0.06 |
| `Nonadditivity.Scalar` | 1 | 4.73 | 2.79 | +0.03 |
| `Nonadditivity.Exact` | 1 | 4.51 | 4.39 | -0.02 |
| `Nonadditivity.Conversion` | 1 | 4.50 | 3.67 | +0.11 |
| `Nonadditivity.Complex` | 1 | 4.41 | 3.55 | +0.09 |
| `Nonadditivity.One` | 1 | 4.41 | 3.25 | +0.00 |
| `Nonadditivity.Small` | 1 | 4.34 | 3.17 | +0.02 |
| `Nonadditivity.Actual` | 1 | 4.33 | 3.30 | +0.02 |
| `Nonadditivity.Regularized` | 1 | 4.03 | 3.12 | +0.04 |
| `Nonadditivity.Canonical` | 1 | 3.97 | 3.19 | +0.04 |
| `Nonadditivity.State` | 1 | 3.75 | 3.08 | -0.13 |
| `Nonadditivity.Strict` | 1 | 3.63 | 3.32 | -0.04 |
| `Nonadditivity.Pure` | 1 | 3.54 | 2.99 | -0.04 |
| `Nonadditivity.Qualitative` | 1 | 3.32 | 3.07 | +0.02 |
| `Nonadditivity.Main` | 1 | 3.27 | 2.91 | -0.03 |
| `Nonadditivity.Purity` | 1 | 3.20 | 2.83 | -0.02 |
| `Nonadditivity.Damping` | 1 | 3.19 | 2.94 | -0.01 |
| `Nonadditivity.Gap` | 1 | 3.11 | 2.55 | +0.01 |
| `Nonadditivity.Switch` | 1 | 2.97 | 2.81 | +0.02 |
| `Nonadditivity` | 1 | 2.83 | 2.84 | +0.09 |
| `All` | 1 | 2.81 | 2.81 | +0.06 |
| `Nonadditivity.Dimensions` | 1 | 2.78 | 2.32 | +0.00 |
| `Nonadditivity.Conjugate` | 1 | 2.67 | 2.42 | -0.01 |
| `Nonadditivity.Conditional` | 1 | 2.64 | 2.52 | +0.02 |

## Warm own-file profiles

Profiles run one at a time after the complete build, without writing oleans.

| Module | Warm wall seconds | Dominant phase | Categorized phase seconds |
| --- | ---: | --- | --- |
| `Audit` | 260.86 | elaboration | elaboration: 253.000; interpretation: 5.580; import: 2.320; blocked (unaccounted): 0.050; initialization: 0.041; compilation (LCNF base): 0.025; linting: 0.019; typeclass inference: 0.017; parsing: 0.013; compilation (LCNF mono): 0.009; compilation (LCNF impure): 0.003; type checking: 0.002; compilation (IR): 0.001; process pre-definitions: 0.001; share common exprs: 0.000; fix level params: 0.000; let-to-have transformation: 0.000; attribute application: 0.000; instantiate metavars: 0.000 |
| `Nonadditivity.NetPolynomial` | 28.88 | typeclass inference | typeclass inference: 29.600; tactic execution: 24.900; simp: 6.830; type checking: 2.740; import: 2.150; elaboration: 1.050; interpretation: 0.822; process pre-definitions: 0.087; linting: 0.069; share common exprs: 0.054; parsing: 0.047; initialization: 0.041; instantiate metavars: 0.033; congr simp thm: 0.024; attribute application: 0.020; fix level params: 0.013; compilation (LCNF base): 0.011; let-to-have transformation: 0.005; compilation (LCNF mono): 0.005; norm_num: 0.004; compilation (LCNF impure): 0.001; compilation (IR): 0.001 |
| `Nonadditivity.RegularFactorization` | 47.86 | typeclass inference | typeclass inference: 70.000; tactic execution: 38.800; type checking: 18.000; simp: 8.720; elaboration: 7.310; import: 2.000; interpretation: 1.700; process pre-definitions: 0.141; share common exprs: 0.122; linting: 0.093; parsing: 0.054; congr simp thm: 0.051; ring: 0.040; attribute application: 0.034; initialization: 0.034; instantiate metavars: 0.034; fix level params: 0.030; norm_num: 0.011; let-to-have transformation: 0.006; compilation (LCNF base): 0.003; compilation (LCNF mono): 0.001; compilation (LCNF impure): 0.000; compilation (IR): 0.000 |
| `Nonadditivity.InitialNetReduction` | 30.86 | typeclass inference | typeclass inference: 33.800; tactic execution: 23.400; simp: 6.250; import: 2.150; type checking: 1.930; elaboration: 1.620; interpretation: 1.430; process pre-definitions: 0.110; linting: 0.098; share common exprs: 0.080; congr simp thm: 0.072; parsing: 0.061; instantiate metavars: 0.042; norm_num: 0.041; initialization: 0.035; ring: 0.033; attribute application: 0.019; fix level params: 0.012; compilation (LCNF mono): 0.006; compilation (LCNF base): 0.005; let-to-have transformation: 0.004; compilation (LCNF impure): 0.002; compilation (IR): 0.001 |
| `Nonadditivity.CollinsYounTensor` | 32.31 | typeclass inference | typeclass inference: 45.600; tactic execution: 7.690; simp: 6.830; import: 2.000; elaboration: 1.670; interpretation: 1.600; type checking: 1.500; process pre-definitions: 0.086; share common exprs: 0.079; linting: 0.073; ring: 0.068; congr simp thm: 0.054; parsing: 0.048; instantiate metavars: 0.046; initialization: 0.035; fix level params: 0.022; attribute application: 0.019; let-to-have transformation: 0.009; norm_num: 0.009; compilation (LCNF mono): 0.005; compilation (LCNF base): 0.004; dsimp: 0.003; compilation (LCNF impure): 0.001; compilation (IR): 0.001; blocked (unaccounted): 0.000 |
| `Nonadditivity.UniversalFactorizationGram` | 26.00 | typeclass inference | typeclass inference: 24.000; type checking: 19.600; tactic execution: 7.700; import: 2.010; elaboration: 1.030; simp: 0.700; interpretation: 0.535; process pre-definitions: 0.054; share common exprs: 0.053; linting: 0.046; initialization: 0.034; congr simp thm: 0.028; parsing: 0.022; fix level params: 0.015; instantiate metavars: 0.015; attribute application: 0.005; ring: 0.004; let-to-have transformation: 0.003; norm_num: 0.002 |
| `Nonadditivity.UniversalFactorizationPolynomialDilation` | 17.47 | typeclass inference | typeclass inference: 14.700; import: 1.990; tactic execution: 0.995; simp: 0.596; type checking: 0.527; elaboration: 0.370; interpretation: 0.347; initialization: 0.032; attribute application: 0.021; linting: 0.018; share common exprs: 0.013; process pre-definitions: 0.010; parsing: 0.009; congr simp thm: 0.007; fix level params: 0.004; instantiate metavars: 0.003; let-to-have transformation: 0.002 |
| `Nonadditivity.NoncommutativeCSSkeletonDecoration` | 18.04 | typeclass inference | typeclass inference: 11.100; simp: 6.160; import: 1.900; tactic execution: 1.710; blocked (unaccounted): 0.940; interpretation: 0.372; type checking: 0.323; elaboration: 0.312; process pre-definitions: 0.055; congr simp thm: 0.042; initialization: 0.032; linting: 0.027; compilation (LCNF base): 0.019; parsing: 0.019; compilation (LCNF mono): 0.010; instantiate metavars: 0.008; share common exprs: 0.008; fix level params: 0.004; compilation (LCNF impure): 0.003; compilation (IR): 0.001; let-to-have transformation: 0.001; attribute application: 0.000 |

## Findings ranked by actionability

- `Audit`: Unattributed elaboration needs declaration tracing and statement/proof isolation before a fix.
- `Nonadditivity.RegularFactorization`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.InitialNetReduction`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.NetPolynomial`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.CollinsYounTensor`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.UniversalFactorizationGram`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.NoncommutativeCSSkeletonDecoration`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.
- `Nonadditivity.UniversalFactorizationPolynomialDilation`: Inspect searched classes and closed/open goals; a cache is not justified without that trace.

Host work floor (4 cores): 767.08s. CPU-weighted import chain: 917.54s. Hypothetical host scheduling is chain-bound; the measured driver itself is serial.

CPU-weighted chain: `Nonadditivity.Linearization` → `Nonadditivity.PositiveLinearization` → `Nonadditivity.RegularCoefficientEnergy` → `Nonadditivity.MatrixRegularRestriction` → `Nonadditivity.RegularDilation` → `Nonadditivity.RegularShiftedDilation` → `Nonadditivity.RegularFactorization` → `Nonadditivity.NetPolynomial` → `Nonadditivity.NetPolynomialSupport` → `Nonadditivity.InitialNetReduction` → `Nonadditivity.StructuredLinearization` → `Nonadditivity.StructuredHaarModel` → `Nonadditivity.HaarWordExpansion` → `Nonadditivity.HaarNonbacktrackingRenewal` → `Nonadditivity.HaarNonbacktrackingLastReturn` → `Nonadditivity.HaarOperatorPolynomial` → `Nonadditivity.HaarOperatorCoefficient` → `Nonadditivity.HaarProfileCoefficient` → `Nonadditivity.HaarProfilePadding` → `Nonadditivity.HaarProfileBlockCoefficients` → `Nonadditivity.HaarProfilePatternBound` → `Nonadditivity.HaarProfileAssignmentBound` → `Nonadditivity.HaarProfileCompositionBound` → `Nonadditivity.HaarSkeletonSegmentation` → `Nonadditivity.HaarDecodedCoefficientBound` → `Nonadditivity.HaarRefinedCoefficientBound` → `Nonadditivity.HaarPrescribedBound` → `Nonadditivity.HaarPrescribedConsequences` → `Nonadditivity.HaarPrescribedScaling` → `Nonadditivity.PrescribedCostScalars` → `Nonadditivity.PrescribedCostDimensions` → `Nonadditivity.PrescribedCostInformation` → `Nonadditivity.PrescribedCostScaling` → `Nonadditivity.PrescribedCostCapacity` → `Nonadditivity` → `Audit` → `All`

Wall-weighted chain: 615.43s.

Measurement only; no elaboration improvement is applied by this harness.

## What is not established

Warm phase totals need not sum to wall time: startup, serialization and other work are not all categorized. Unattributed elaboration is not a proof-tactic diagnosis. Events under Lean's profiler threshold are absent from individual listings.
Peak RSS is a maximum, not a sum across files. The full-build number includes the Python and wrapper processes. Compiler startup and wrapper/guard overhead are included in full-build wall time.
Dependency guards compare stat provenance before/after; they do not prove that a mutation was made and perfectly restored between snapshots. Own sources are stat-polled and hash-checked. Other processes are disclosed, not treated as evidence of contamination.
Two snapshots do not establish a monotonic trend. Family labels use the first CamelCase component of the flat module filename (for example Haar or Operational); they are not parsed Lean namespace declarations.

## Methodology

```sh
/opt/hostedtoolcache/Python/3.11.17/x64/bin/python /home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/scripts/elaboration_test.py --label after --output /home/runner/work/_temp/elaboration-evidence/after --time-bin /usr/bin/time --prior-summary /home/runner/work/_temp/elaboration-evidence/before/summary.json
# Actual timed full-build command
/usr/bin/time -v -o /home/runner/work/_temp/elaboration-evidence/after/build.time.txt /home/runner/work/Holevo-Additivity-Gap/Holevo-Additivity-Gap/build.sh
```

Per-module raw stdout/stderr and GNU time output are in `logs/` and `timings/`; exact compiler commands are in `measurements.jsonl`. `summary.json` retains source hashes, build coverage, phase events, dependency provenance pointers and guard outcomes.

## Pointers

Prior summary: `/home/runner/work/_temp/elaboration-evidence/before/summary.json`.

Comparability: Compiler, GNU time, core count and host match; processes and warm caches can still introduce noise.
