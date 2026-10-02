# Holevo Additivity Gap

Lean 4 proofs accompanying Jinzhao Wang's manuscript on unbounded Holevo additivity gaps. The development constructs actual finite-dimensional CPTP channels, proves quantitative dimension and information bounds, and derives operational classical-capacity and input-cost consequences. The toolchain is pinned to Lean `4.29.0-rc6` and mathlib commit `f156f7abd91ac67adb22bf999e5a71ba22e22e41`.

**The full manuscript is not formalized.** The principal endpoints below have no unproved analytic or coding premises. Two intermediate counting arguments are repaired in Lean; the included [manuscript](paper/nonadditivity.tex) is the original, uncorrected source. Read the [scope and limitations](docs/FORMALIZATION_STATUS.md) and [manuscript corrections](docs/CORRECTIONS.md).

## The statements

Write `χ(T)` for single-use Holevo information in bits, `χ₂(T) = χ(T ⊗ T)`, and `C(T)` for unassisted classical capacity defined by physical codes and vanishing decoding error.

| Result | Statement and source |
| --- | --- |
| Prescribed dimensions and gap | For `K ≥ 2`, `n ≥ ⌈256(1 + ln K)²⌉`, construct input dimension `2NⁿK²ⁿ`, output dimension `Kⁿ`, with `N = ⌈exp(40(7 ln K + 2)n)⌉`, positive `χ(T)`, and explicit one-use, two-use, and gap bounds. [Exact statement](Nonadditivity/HaarPrescribedBound.lean); [formulas](docs/FORMALIZATION_STATUS.md#prescribed-dimensions-and-information-gap). |
| Arbitrarily large separation | For every `ε > 0` and real `A, R`, a channel satisfies `0 < χ(T) ≤ ε`, `C(T) − χ(T) ≥ A`, and `χ₂(T)/(2χ(T)) ≥ R`. [Exact statement](Nonadditivity/OperationalConsequences.lean). |
| Operational coding theorem | `C(T) = supₘ≥₁ χ(T⊗ᵐ)/m`, with convergence of the normalized tensor-power quantities. Both sides are independently defined. [Exact statements](Nonadditivity/OperationalCodingTheorem.lean). |
| Scaling and further endpoints | Fixed-`K` gaps are linear in output qubits and proportional to the square root of input qubits when `δ_K > 0`; growing-`K` input-cost bounds and all-use Weyl identities are also proved. [Result catalog](metadata/results.json); [proof route](PROOF-PATH.md). |

These results concern `χ₂(T) − 2χ(T)` and `C(T) − χ(T)`. They do not assert nonadditivity of operational capacity between distinct channels. The exact Lean types and definitions determine what has been proved; the catalog connects 25 manuscript/result records to 49 named declarations.

## How it was verified

| Check | Recorded result |
| --- | --- |
| Full project-source Lean rebuild | [GitHub CI run 36901743100, attempt 2](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/36901743100/attempts/2), commit `141f355`: 369 project modules rebuilt; build, transitive axiom audit, metadata validation, and all local challenge checks passed. Mathlib dependencies came from the pinned cache. |
| Axiom audit | 9,107 project declarations and 7,219 theorem constants; only `propext`, `Classical.choice`, and `Quot.sound` are permitted. No unfinished proofs or project-specific axioms in the proof library. |
| Comparator | Five challenge modules and six solution/expected-type checks passed locally. **End-to-end Comparator execution has not been performed.** |
| Independent kernel | **Not run.** No nanoda verification is claimed. |

[Saved CI evidence](verification/github-actions-141f355.json) and [verification records](verification/README.md) distinguish the new source rebuild from the earlier audit using cached project objects. The audit also covers private helpers and definitions containing proof fields. It does not establish that the formal statements express the intended manuscript claims; that requires reviewing the [correspondence catalog](metadata/results.json) and [proof map](docs/PROOF_MAP.md).

## Check it yourself

For Linux or macOS, install [elan](https://github.com/leanprover/elan) and have Git and Python 3.11 or later with `venv`/`pip` available (Debian/Ubuntu may need `python3-venv`). A network connection is required for pinned dependencies. From a fresh checkout:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git
cd Holevo-Additivity-Gap
./verification/lean/run.sh
```

The script installs validation packages in an isolated environment, downloads the pinned mathlib cache, rebuilds every project proof module, audits transitive axioms, validates metadata and named declarations, and checks all five challenge statements against the six solution proofs. See [the script](verification/lean/run.sh) for the exact commands. Build warnings are retained and do not by themselves indicate a failed check.

Successful checks report `BUILD PASSED:`, `AUDIT PASSED:`, `DECLARATIONS PASSED:`, and `RELEASE CHECKS PASSED:`, and write a challenge report with `"status": "passed"`. The script finishes with `LEAN REPRODUCTION PASSED` and exits zero only after every step succeeds. Per-step logs and copied reports are retained in `.verify-work/logs/lean-<timestamp>-<process ID>/`; the audit log is `.lake/check.log`, declaration log is `.lake/release-declarations.log`, validation report is `.lake/release-validation.json`, and challenge logs/report are `.lake/challenge-checks/` and `.lake/challenge-checks.json`.

To run individual checks after the reproducer has prepared dependencies:

```sh
. .verify-work/python-env/bin/activate
./check.sh                            # full project-source rebuild and axiom audit
python3 scripts/validate_release.py    # metadata, source integrity, and Lean declaration checks
python3 scripts/check_challenges.py    # local expected-statement and solution/type checks
```

For a genuine Comparator check, use **Linux**, a nonroot account, a working systemd user session, and [landrun](https://github.com/Zouuup/landrun) on `PATH`. Use a separate fresh checkout and run Comparator before compiling project proofs outside its sandbox:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git Holevo-Comparator-Check
cd Holevo-Comparator-Check
./verification/comparator/run.sh
```

This fetches and builds the pinned matching Comparator and exporter, then runs every challenge with the upstream systemd sandbox guard. See [the script](verification/comparator/run.sh) and [challenge trust assumptions](ComparatorChallenges/README.md). Each successful Comparator log must contain `Your solution is okay!`; the script finishes with `COMPARATOR REPRODUCTION PASSED`. Per-configuration logs and exit status are retained in `.verify-work/logs/comparator-<timestamp>-<process ID>/`, with checker work under `.verify-work/comparator/`. The expected-statement files contain six deliberate `sorry` placeholders and are excluded from the proof library and its audit. Local type checks are separate from the Comparator run.

## Reading the proof in a browser

The [documentation website](https://JWang226.github.io/Holevo-Additivity-Gap/) provides the proof route, exact Lean statements and source, and searchable links into the development. [PROOF-PATH.md](PROOF-PATH.md) is the short reading guide; [docs/PROOF_MAP.md](docs/PROOF_MAP.md) gives the detailed manuscript map.

The generated pages are included in `html/`. Open `html/index.html` directly for offline browsing, or serve the checkout locally:

```sh
python3 -m http.server 8000 --directory html
```

Then open <http://localhost:8000/>. The site is a reading aid, not an additional proof checker. Lean source is authoritative; the mathematical roadmap is not the complete kernel dependency graph.

## Sources and attribution

| Artifact | Purpose |
| --- | --- |
| [Nonadditivity/](Nonadditivity/) | Proofs, definitions, constructions, and explicit conditional interfaces |
| [All.lean](All.lean), [Audit.lean](Audit.lean) | Aggregate build target and transitive axiom audit |
| [formalization.yaml](formalization.yaml), [metadata/results.json](metadata/results.json) | Machine-readable formalization status and manuscript correspondence |
| [ComparatorChallenges/](ComparatorChallenges/) | Separate expected statements and pinned checker configurations |
| [verification/](verification/) | Reproducer scripts and recorded verification evidence |
| [docs/AI_USAGE.md](docs/AI_USAGE.md) | AI assistance and available provenance |

The reader organization is inspired by [Anthropic's Fermat project](https://github.com/anthropics/fermats-last-theorem); the metadata/challenge layout follows [OpenAI's ten-proofs](https://github.com/openai/ten-proofs) and [AGM's formalization guidance](https://agmai.org/general-sep29/). The documentation and proofs here are specific to this project; no affiliation with those labs is implied.

Original project material has no blanket open-source license selected. Copyright and existing third-party notices are preserved in [COPYRIGHT.md](COPYRIGHT.md) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). [Remaining review and verification work](docs/RELEASE_CHECKLIST.md) includes manuscript corrections and the pending external checks.
