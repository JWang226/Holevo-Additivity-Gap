<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# v1.0.0

Lean 4 certificates for the principal results in
[*Unbounded Holevo additivity gaps in finite dimensions*](https://arxiv.org/abs/2609.18222),
with an offline proof browser, manuscript mappings,
reproduction commands, and retained verification evidence.

The six challenge roots cover prescribed channel dimensions, the operational
coding identity, small one-use Holevo information with large capacity gain and two-use ratio,
Weyl extension identities for positive tensor powers, and two input-cost bounds.
The full manuscript is not formalized. See
[formalization scope](FORMALIZATION_STATUS.md) and
[statement correspondence review](STATEMENT_AUDIT_DELTA.md) for qualifications.

The revised manuscript incorporates the [two counting repairs](CORRECTIONS.md)
recorded during formalization.

## Cleanup

- Removed 50 redundant direct imports across 40 files while preserving the
  transitive local import closures.
- Retained the measured `RegularCoefficientEnergy` reindexing improvement:
  36.9% lower module CPU time across repeated controlled trials.
- Preserved all 5,323 public declaration types and six challenge-root types.
- The two recorded full builds took 36m 08.55s and 36m 02.44s; these descriptive
  measurements do not establish a whole-build speedup.
- Kept the 104 existing warnings and documented legacy module-header limits.

The [cleanup report](../verification/elaboration-20261006/README.md) includes
raw profiles, rejected trials, source hashes, and reproduction instructions.

## Release verification

[Normal Lean CI run 37577412043](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/37577412043)
passed on release-source commit `38b360705c55fe4ee28e52f6cc493495fb7c1955`.
It rebuilt all 369 project modules, audited 9,107 declarations / 7,219 theorem
constants, and checked 49 mapped declarations and six expected types.
The [execution record](../verification/github-actions-release-38b36070.json)
and [verbatim excerpt](../verification/github-actions-release-38b36070-excerpt.log)
retain the actual results and source bindings. This job did not run Comparator
or Nanoda.

The all-mode proof verifier and archive in
[run 37577412179](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/37577412179)
passed on the same source commit: a fresh Lean rebuild/audit, Comparator
statement comparisons and Lean replay, Nanoda independent kernel checks, and
all 13 acceptance/rejection controls. The
[full-run summary](../verification/portable-20261007/run-summary.json) retains
those results. The **overall job failed** afterward during statement-axiom
recording, after fresh declaration export passed; its website step was skipped.
The [job record](../verification/github-actions-release-all-38b36070.json) and
[excerpt](../verification/github-actions-release-all-38b36070-excerpt.log)
preserve that failure.

The [statement continuation](../verification/statement-audit-current.json)
now records the completed original Linux expected-statement applications and
root-axiom checks from `38b36070`. Their outputs were
[recovered from the verified job artifact](../verification/statement-audit-20261007/recovery.json),
with no proof commands rerun. The original checks used the fresh Linux project
objects; that run's declaration export matched the frozen metadata. The
original recorder driver's argument list was
not retained. All six qualified correspondence findings remain qualified;
no complete semantic audit, machine-certified English–Lean equivalence or
independent human certification is claimed. Both current evidence freshness
checks pass.

Reproduce all checks with:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

Lean is pinned to `leanprover/lean4:v4.29.0-rc6`; Mathlib and independent checkers
retain their recorded source pins. The dependency cache is reused, and all
369 project proof modules are rebuilt. The permitted transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Comparator and Nanoda execute
unsandboxed on trusted sources. See [verification instructions](verify.md).

The [proof website](https://jwang226.github.io/Holevo-Additivity-Gap/) and `html/index.html` provide the results, concept guides,
proof map, manuscript-to-Lean map, exact declarations, and source browsing.
The source archives include this offline website and the recorded evidence.

## Citation and licensing

Cite the manuscript together with repository tag `v1.0.0`; the citation metadata
identifies software version `1.0.0`. No DOI is claimed. Original project material
retains its existing copyright status; a blanket open-source license has not
been selected. Third-party attribution and licenses remain preserved in
`COPYRIGHT.md`, `THIRD_PARTY_NOTICES.md`, and `LICENSES/`.
