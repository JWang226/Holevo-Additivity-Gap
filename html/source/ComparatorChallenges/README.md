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

The portable workflow checks these six configurations and seven theorem roots using
Comparator’s comparison/axiom APIs and Lean kernel replay. A separate Nanoda
mode checks the exported solution proofs with an independent Rust kernel.
See [verification evidence](../verification/README.md) for recorded execution.
Both modes run unsandboxed on trusted local sources.

The `enable_nanoda: false` field disables the optional Nanoda path in
Comparator's configuration interface. The portable `nanoda` and `all` modes
run Nanoda separately on every listed solution root and require that field
to remain false.

## Contents

| Configuration | Solution module | Result |
| --- | --- | --- |
| `A_PrescribedDimensions.json` | `Nonadditivity.HaarPrescribedBound` | Exact finite dimensions, positive one-use information, the one-use upper bound, and the two-use gap |
| `B_OperationalCoding.json` | `Nonadditivity.OperationalCodingTheorem` | Capacity of physical codes equals the regularized Holevo supremum |
| `C_SmallInformationSeparation.json` | `Nonadditivity.OperationalConsequences` | Arbitrarily small positive one-use information with arbitrarily large operational gain and two-use ratio |
| `D_WeylAllUses.json` | `Nonadditivity.WeylPowersEntropy` | Exact Weyl-extension Holevo identity at every positive tensor power |
| `E_InputCost.json` | `Nonadditivity.PrescribedCostCapacity` | One-use information bounds and two-use/operational lower bounds in terms of actual input-qubit cost |
| `F_TwoUseSeparation.json` | `Nonadditivity.DeterministicConsequences` | Arbitrarily small positive one-use information with arbitrarily large absolute two-use information per use |

Each JSON file lists the exact fully qualified theorem names. There are no
unfilled definition holes. The repeated definition `inputLogScale` in challenge
E has the same concrete value as the solution definition.

C does not directly assert the absolute two-use separation `chiTwo / 2 ≥ R`
in manuscript `cor:separation`. F checks that endpoint through
`Nonadditivity.DeterministicConsequences.actual_small_large`, strengthened by
positive one-use information and an arbitrary real `R`. The divergent-sequence
and capacity assertions are separately proved consequences, outside F's root.

The challenge modules deliberately contain `sorry` for their expected theorem
statements. These seven placeholders are **not proof certificates**. The proof
library and `Audit.lean` never import the challenge modules. The configurations
permit only `propext`, `Quot.sound`, and `Classical.choice`, so a solution whose
proof depends on `sorryAx` is not permitted.

## What is trusted and what is checked

Each challenge explicitly writes its expected statement and imports selected
lower-level project modules needed to define it. It does not import its target
solution module or the target theorem. Those imports include previously proved
lemmas, not just primitive definitions. For example, C imports
`Nonadditivity.OperationalCodingTheorem`, including the theorem checked
separately by B, because that module also defines the operational
`classicalCapacity` wrapper. These shared proof dependencies are included in
the solution exports checked by Lean replay and Nanoda; independent kernel
checking does not mean disjoint proofs. E imports the construction and
logarithmic input-cost infrastructure.

Review the challenge's complete import closure, its definitions of channels and
information quantities, and the Lake configuration as trusted statement material.
The challenge suite does not independently reimplement those mathematical
objects or establish that they express the intended natural-language claims.
The manuscript mapping and proof map support that separate human review.

Comparator mode compares the statements and their definition
dependencies, rejects nonpermitted axioms in the solution proof dependencies,
and replays the solution through Lean’s kernel. Nanoda mode independently
checks the solution exports. Local elaboration and `Audit.lean` are separate checks.

## Reproducible tool versions

The main project remains pinned to Lean `v4.29.0-rc6`. A matching upstream
Comparator tag exists:

| Component | Pinned revision |
| --- | --- |
| Comparator (`v4.29.0-rc6`) | `a4f696825c583ed8a5b4060d9a0faa5b882d365b` |
| `lean4export` from that Comparator manifest | `048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` |
| `Lean4Checker` from that Comparator manifest | `b7398199245524275543dec6113229c9bb4902e5` |

The portable wrapper builds this pinned checker in `.verify-work/comparator/`
without altering the main proof dependency manifest. Nanoda and Rust pins are
recorded in [verification/nanoda/toolchain.json](../verification/nanoda/toolchain.json).

## Running the checks

From the repository root on macOS or Linux:

```sh
bash scripts/verify.sh comparator
bash scripts/verify.sh nanoda
```

Or reproduce the full Lean build, statement comparison, kernel replay, and
independent kernel check with:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/additive-20261008/source-certificate.json
```

This explicitly selects the additive extension of the recorded rebuild/type
certificate for the new challenge of an existing theorem. Without
`--source-certificate`, the validator retains its historical byte-equality
gate. The certificate does not replace the fresh proof checks or change
historical evidence bindings.

No landrun or systemd is required. Every failed stage returns a nonzero exit
code. Success reports and logs are retained under `.verify-work/run-*`.
Comparator prints `LOCAL DIAGNOSTIC PASSED` for each configuration; Nanoda
prints `NANODA PASSED (UNSANDBOXED)` for each configuration. These labels do
not claim sandboxed upstream CLI execution.

See [docs/verify.md](../docs/verify.md) for prerequisites, acceptance/rejection
controls, exact checker pins, expected output, and binary provenance.

For the separate local elaboration/type-fit checks after building the proofs:

```sh
python3 scripts/check_challenges.py
```

This creates scratch modules retaining the expected types and proves them using
the actual solution theorems. For E, it verifies the concrete `inputLogScale`
definition before reusing the solution definition. Logs and generated checks
are in `.lake/challenge-checks/`; the record is `.lake/challenge-checks.json`.
This elaboration check alone is separate from Comparator or Nanoda execution.
