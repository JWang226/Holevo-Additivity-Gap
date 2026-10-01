<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-->

# Comparator challenges

These files follow the separate statement/configuration pattern used by
[openai/ten-proofs](https://github.com/openai/ten-proofs/tree/main/ComparatorChallenges)
and the [Comparator configuration interface](https://github.com/leanprover/comparator).
The statements and explanations here were written for this project. No
third-party proof code or README text was copied from those repositories.

**Status:** the five challenge modules elaborate under the pinned Lean version,
and their six expected statements accept the corresponding solution proofs.
An end-to-end Comparator run has **not** been performed. Neither a successful
Comparator run nor a nanoda check is claimed by this release.

## Contents

| Configuration | Solution module | Result |
| --- | --- | --- |
| `A_PrescribedDimensions.json` | `Nonadditivity.HaarPrescribedBound` | Exact finite dimensions, positive one-use information, the one-use upper bound, and the two-use gap |
| `B_OperationalCoding.json` | `Nonadditivity.OperationalCodingTheorem` | Capacity of physical codes equals the regularized Holevo supremum |
| `C_SmallInformationSeparation.json` | `Nonadditivity.OperationalConsequences` | Arbitrarily small positive one-use information with arbitrarily large operational gain and two-use ratio |
| `D_WeylAllUses.json` | `Nonadditivity.WeylPowersEntropy` | Exact Weyl-extension Holevo identity at every positive tensor power |
| `E_InputCost.json` | `Nonadditivity.PrescribedCostCapacity` | One-use information bounds and two-use/operational lower bounds in terms of actual input-qubit cost |

Each JSON file lists the exact fully qualified theorem names. There are no
unfilled definition holes. The repeated definition `inputLogScale` in challenge
E has the same concrete value as the solution definition.

The challenge modules deliberately contain `sorry` for their expected theorem
statements. These six placeholders are **not proof certificates**. The proof
library and `Audit.lean` never import the challenge modules. The configurations
permit only `propext`, `Quot.sound`, and `Classical.choice`, so a solution whose
proof depends on `sorryAx` is not permitted.

## What is trusted and what is checked

Each challenge explicitly writes its expected statement and imports selected
lower-level project modules needed to define it. It does not import its target
solution module or the target theorem. Those imports include previously proved
lemmas, not just primitive definitions. For example, C imports the module that
defines the operational `classicalCapacity` wrapper; E imports the construction
and logarithmic input-cost infrastructure.

Review the challenge's complete import closure, its definitions of channels and
information quantities, and the Lake configuration as trusted statement material.
The challenge suite does not independently reimplement those mathematical
objects or establish that they express the intended natural-language claims.
The manuscript mapping and proof map support that separate human review.

Comparator is intended to compare the statements and their definition
dependencies, reject nonpermitted axioms in the solution proof dependencies,
and replay the solution through its kernel checker. Local elaboration and the
project's `Audit.lean` are useful checks but are not substitutes for that run.

## Reproducible tool versions

The main project remains pinned to Lean `v4.29.0-rc6`. A matching upstream
Comparator tag exists:

| Component | Pinned revision |
| --- | --- |
| Comparator (`v4.29.0-rc6`) | `a4f696825c583ed8a5b4060d9a0faa5b882d365b` |
| `lean4export` from that Comparator manifest | `048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` |
| `Lean4Checker` from that Comparator manifest | `b7398199245524275543dec6113229c9bb4902e5` |

Build Comparator separately using that checkout and its committed
`lake-manifest.json`; do not run `lake update` there, since its unpinned
`lean4export` input revision would otherwise move. This keeps the main proof
project's dependency manifest unchanged.

```sh
git clone https://github.com/leanprover/comparator.git
cd comparator
git checkout a4f696825c583ed8a5b4060d9a0faa5b882d365b
lake build comparator lean4export
```

A genuine sandboxed run requires Linux with working `landrun` and a compatible
`lean4export` on `PATH`. Follow the current
[Comparator installation and sandbox guidance](https://github.com/leanprover/comparator#readme).
The pinned Comparator does not itself install those external executables.
The JSON configurations use the Lean checker; additional nanoda checking is
optional and has not been enabled or performed.

## Running the checks

From a fresh project checkout on a suitable Linux machine, obtain the trusted
mathlib cache. Set `NONADDITIVITY_COMPARATOR_BIN` to the absolute path to the
separately built Comparator executable and put the compatible `lean4export`
and `landrun` executables on `PATH`.

```sh
lake exe cache get
export NONADDITIVITY_COMPARATOR_BIN=/absolute/path/to/comparator/.lake/build/bin/comparator
```

For a statement elaboration check only, run:

```sh
lake build ComparatorChallenges
```

After the proof library has been built, reproduce both local checks with:

```sh
python3 scripts/check_challenges.py
```

This script compiles each challenge separately, then creates scratch modules
that retain its explicit expected theorem types and prove them using the actual
solution theorems. It transforms only the six identified theorem placeholders.
For E, it verifies the repeated concrete `inputLogScale` definition before
reusing the solution definition. It does not rebuild baseline proof modules.
The relative logs and generated checks are in `.lake/challenge-checks/`; the
machine-readable result is `.lake/challenge-checks.json`. Both local checks are
distinct from running Comparator.

For the actual Comparator check, use the current upstream-recommended systemd
sandbox guard. For example, check A with:

```sh
systemd-run --user --pty --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" -E PATH="$PATH" \
  -E NONADDITIVITY_COMPARATOR_BIN="$NONADDITIVITY_COMPARATOR_BIN" \
  bash -c 'lake env "$NONADDITIVITY_COMPARATOR_BIN" ComparatorChallenges/A_PrescribedDimensions.json'
```

Repeat with B, C, D, and E. Preserve each command, exit code, full log, and tool
revision before changing the recorded Comparator status to verified. Do not
replace `landrun` with an unsandboxed compatibility script and report the result
as an independent sandboxed verification.
