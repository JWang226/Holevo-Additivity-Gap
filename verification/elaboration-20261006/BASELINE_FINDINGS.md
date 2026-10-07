# Interpretive findings from the baseline and cleanup trials

The timed baseline is commit `743cc95bc4c0b1bca891994def26d9e5f8c7aad6`, **after** the dead-code sweep. It is valid: all 369 production modules were measured and compiled successfully, with no missing, duplicated, unexpected, or failed modules. This section explains the completed baseline and the separate A/B decisions; the matched full-after figures belong in the before/after comparison.

## Baseline scope and health

| Observation | Baseline |
|---|---:|
| Production Lean files | 369 |
| Production physical / non-comment code lines | 57,473 / 44,492 |
| Whole Git tree Lean files | 768 |
| Whole Git physical / code lines | 115,995 / 89,728 |
| Full build wall time | 2,168.55 s (36 min 8.55 s) |
| Full build CPU, user + system | 3,142.12 s |
| Summed own compiler CPU | 3,076.49 s |
| Full build peak RSS | 4,531,316 KiB |
| Errors / sorry warnings / unauthorized sorry tokens | 0 / 0 / 0 |
| Existing warnings | 104 |

The baseline ran on one Linux x86-64 four-core runner with pinned Lean 4.29.0-rc6. The project driver compiled one module at a time; Lean retained its default internal threading, with no `-j` override. GNU time reported 144% CPU for the complete build, so “serial driver” does not mean that every Lean invocation used only one CPU. Dependencies were cached inputs, not rebuild targets. Source and cached-artifact guards reported no mutation.

The 104 warnings comprise 77 unused-variable/argument warnings, 19 unnecessary `<;>` warnings, seven `simp`/`simpa` suggestions, and one deprecation warning. A successful no-sorry build therefore does not imply a warning-free project. Removing unused public parameters would alter exported statements; they were not silently removed as dead code.

## Where the baseline time goes

| Slowest eight by full-build wall time | Full wall s | Full CPU s | Warm own-file wall s | Warm own-file CPU s |
|---|---:|---:|---:|---:|
| `Audit` | 261.22 | 261.64 | 259.13 | 259.53 |
| `NetPolynomial` | 62.05 | 102.88 | 28.33 | 68.77 |
| `RegularFactorization` | 48.29 | 146.38 | 47.19 | 145.74 |
| `InitialNetReduction` | 36.37 | 76.07 | 29.13 | 70.99 |
| `CollinsYounTensor` | 32.31 | 67.37 | 32.01 | 67.27 |
| `UniversalFactorizationGram` | 26.63 | 55.55 | 25.91 | 55.52 |
| `RegularCoefficientEnergy` | 18.09 | 22.16 | 17.94 | 22.07 |
| `NoncommutativeCSSkeletonDecoration` | 18.04 | 21.86 | 17.76 | 21.58 |

The full-build heavy tail contains **23 files at least 10 s, 6 at least 20 s, 5 at least 30 s, and 3 at least 40 s**. These eight files were then profiled serially without writing compiler artifacts. Full-build figures include output construction and the measured build environment; warm own-file profiles isolate a different operation. For example, NetPolynomial is 62.05 s in the build and 28.33 s in the warm profile. That difference is not itself an optimization or a measured causal decomposition.

| Largest filename families by summed own CPU | Files | CPU s | Share of own CPU | Summed wall s |
|---|---:|---:|---:|---:|
| `Haar` | 167 | 890.13 | 28.9% | 667.42 |
| `Regular` | 6 | 268.46 | 8.7% | 119.77 |
| `Audit` | 1 | 261.64 | 8.5% | 261.22 |
| `Collins` | 4 | 124.53 | 4.0% | 60.23 |
| `Net` | 3 | 116.52 | 3.8% | 69.91 |
| `Universal` | 5 | 116.51 | 3.8% | 67.22 |
| `Product` | 9 | 111.87 | 3.6% | 68.67 |
| `Noncommutative` | 11 | 110.20 | 3.6% | 78.58 |

These groups use reproducible filename prefixes in a flat source directory; they are not parsed Lean namespaces. Haar has the largest aggregate cost because it spans 167 files, while the six-file Regular family concentrates substantial cost in factorization and Hilbert-space operations. Group size alone is not evidence for applying the same optimization to every member.

## Phase routing and retained scope

| Warm module | Largest cumulative phase | Seconds | Interpretation |
|---|---|---:|---|
| `Audit` | elaboration | 251.00 | Intended axiom-integrity work; retain the audit. |
| `NetPolynomial` | typeclass inference | 29.90 | Investigate actual class targets / theorem application order; no import-driven proof rewrite. |
| `RegularFactorization` | typeclass inference | 69.70 | Diffuse operator/Hilbert class resolution plus costly checking; no cache justified by a head-name count alone. |
| `InitialNetReduction` | typeclass inference | 34.70 | Class-resolution route, subject to a target trace; leave unchanged in this pass. |
| `CollinsYounTensor` | typeclass inference | 45.20 | Class-resolution route; avoid cache rollout by similarity. |
| `UniversalFactorizationGram` | typeclass inference | 23.80 | Class resolution and a large checking event; tested helper extraction failed and was reverted. |
| `RegularCoefficientEnergy` | tactic execution | 9.29 | Localize the expensive summability application; explicit summand succeeded. |
| `NoncommutativeCSSkeletonDecoration` | typeclass inference | 10.90 | Class resolution and simp; no demonstrated local change retained. |

The cleanup skill routes work only after a phase exceeds both 5 s and 25% of categorized work. The warm imports here cost approximately **1.88–2.36 s**, below that floor. Import-load reduction was consequently not the route for the measured heavy tail. The earlier non-redundant import candidates for OperationalBlockRates and FiniteFreeModel were prepared for review but not applied: their complete baseline builds were only 3.22 s and 3.15 s, and removal safety would still need fresh elaboration and a public-type check. Their static absence of old proof references is not proof that imported instances, simp attributes, scopes, or tactics are dispensable.

NetPolynomial has cumulative typeclass inference 29.9 s, tactic execution 25.3 s, and simp 6.66 s. RegularFactorization has typeclass inference 69.7 s, tactic execution 38.8 s, type checking 17.8 s, and simp 8.37 s. Cumulative counters describe work that can occur under Lean internal parallelism; they are not a list of disjoint additions to elapsed wall time. Named events below 100 ms are omitted, and a large tactic event may include class/unification work.

The displayed class events are diffuse. In NetPolynomial, Algebra accounts for 18 visible events totaling 3.676 s; no CStarAlgebra event exceeds the reporting threshold. In RegularFactorization, the leading visible families are AddCommMonoid (58 events, 7.087 s), CoeFun (28, 6.753 s), and TopologicalSpace (52, 6.394 s). These totals neither identify concrete instance goals nor justify caching derived classes. A known parameterized carrier can be a closed search; a carrier still represented by a metavariable is open. Closed head-class caching would require the actual recurring target, placement outside section-variable scopes, and a separate A/B win. No cache was retained.

`Audit.lean` is the largest wall-time item: its warm elaboration counter is 251 s. The retained raw log reports **9,107 project declarations, 7,219 theorems**, and only `propext`, `Quot.sound`, and `Classical.choice` in the transitive axiom set. Its explicit axiom inspections and complete project closure audit are intentional integrity checks. The skill’s advice about removing accidental debug `#` commands does not justify deleting this dedicated audit to make the timing table smaller.

## A/B decisions

Each valid experiment used three baseline and three candidate warm profiles, alternating variants on the same runner. Source, tool, and artifact guards were retained. The final selected cleanup source is `e943a85f0234a573477a10871f60a2d9583fa47b`: the 50 already-swept imports plus one explicit summand in RegularCoefficientEnergy.

| Trial | Decision | Evidence |
|---|---|---|
| 1: RegularCoefficientEnergy summability application | Retained | Median tactic execution 9.24 → 1.14 s (−87.7%); wall 17.92 → 9.84 s (−45.1%); CPU 22.03 → 13.91 s (−36.9%). All six runs valid. |
| 2: NetPolynomial spectral theorem type ascription | Reverted as null | Median wall 28.81 → 28.94 s; CPU 69.03 → 69.26 s; TC 29.7 → 30.2 s. No ≥2 s or ≥10% relevant-phase improvement. All six runs valid. |
| 3: UniversalFactorizationGram private sandwich helper | Reverted as invalid | All three candidate runs hit the existing 1,000,000-heartbeat limit; all three baseline runs passed. Failed-run timings are diagnostic evidence, not a successful before/after benchmark. |

The retained change gives `Equiv.summable_iff` its actual summand, `fun g : G => ‖f g‖ ^ (2 : ℝ≥0∞).toReal`, before supplying the existing summability proof. It leaves declaration signatures, the mathematical construction, and hypotheses unchanged. Its measured gain is in tactic execution; median TC is essentially unchanged (8.52 → 8.51 s), so the evidence does not support calling this a class-cache improvement. Small increases in other counters, such as checking 0.617 → 0.639 s, are visible in the raw evidence and are negligible against the sustained ~8.1 s saving.

The null and failed experiments were removed rather than combined with the successful one. The failed Gram helper did not trigger a heartbeat increase. No speculative import shrinking, module splitting, public declaration move, or blanket simp rewrite was included.

## Method limits that remain explicit

- **The 50 redundant imports precede the baseline.** They were removed in 40 files after checking identical local transitive import closures; no safe helper deletion was found. The two timed snapshots cannot measure their performance contribution because there is no matched pre-sweep snapshot. The A/B trial separately attributes the summand-annotation gain.
- **Full before/after results are observational.** Even on the same runner with the same compiler, cache, driver, and timing tools, two full rebuilds can differ in internal scheduling and contention. The repeated isolated trial provides the causal evidence for the retained intervention; an unrelated file improving in the second full build is not automatically a downstream benefit.
- **The modern module-header criterion is unmet.** All 369 production files, and all 768 counted Git-tree Lean files, remain in legacy non-`module` syntax. This is recorded as an explicit adaptation of the elaboration-test skill, not a pass of its zero-legacy-files expectation. Migrating exports to modern `module`/`public` syntax is a separate API migration.
- **The scheduling bound is hypothetical.** The snapshot’s four-core CPU work floor is 769.12 s, versus a weighted CPU dependency chain of 928.26 s. This marks a hypothetical parallel-module schedule as chain-bound on this machine shape. The actual measurement used a serial project driver; these numbers do not predict its observed wall time.
- **Lean integrity is narrower than manuscript correspondence.** The successful audit does not establish complete manuscript coverage or English-to-Lean equivalence. Final-state public-type preservation requires the fresh source-bound export comparison; it must not be inferred solely from unchanged printed statements.

Raw baseline provenance, the complete 369-module inventory, tiers, top 30, source census, eight warm profiles, and measurement logs are in the retained baseline artifact. Raw three-versus-three results are in the three trial artifacts; rejected trial data remains reviewable.
