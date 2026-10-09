# arXiv v2 and the absolute two-use separation root

This is a source-delta AI review of the exact published arXiv source
[2609.18222v2](https://arxiv.org/abs/2609.18222v2), revised October 5, 2026,
and the added `F_TwoUseSeparation` challenge. It continues the historical
six-root reviews with their qualifications and explicitly corrects root C's
coverage description. It does not claim a repeated full independent semantic
review, human certification, or machine-certified English–Lean equivalence.

The manuscript SHA-256 is
`18c4c60a8494f4421e8e356d75dcee81df93beace7de3bfdc8274b719df68736`.
[Source provenance](../paper/arxiv-v2.json) binds the original arXiv archive
and its `nonadditivity.tex` member. The repository manuscript has exactly those
upstream bytes, without the proposed local scope-wording corrections.

## Reviewed delta

All 85 manuscript labels are retained. The containing statement blocks for
`eq:def-chi`, `eq:def-smin`, `eq:capacity`, `thm:main`, `cor:capacity`,
`cor:separation`, `rem:separation-cost`, `eq:chi-extension`, `lem:haar`,
`eq:positive-probability`, and `lem:cy` are byte-identical to the predecessor
repository manuscript. The changes relocate discussion of the repaired
Bordenave–Collins counts, add concurrent-work discussion and references,
change the AI-usage sentence, and revise exploration-mark proof prose.
The concurrent works' claims and relative resource costs were not independently
reviewed in this continuation.

All 369 production proof-source files, the declaration export, and the original
five challenges are unchanged. F adds an expected statement for an already
exported public theorem; it adds no production theorem or assumption.
The [additive source certificate](../verification/additive-20261008/source-certificate.json)
validates these boundaries and the sole appended Lake challenge root. It does
not itself claim a new build, expected-statement application, Comparator run,
or Nanoda run.

## Root correspondence

| Root | Reviewed endpoint | Current finding |
| --- | --- | --- |
| A | `thm:main`, prescribed finite dimensions and information bounds | Existing qualified finding retained. The root also gives positive one-use information and its same-witness lower bound. |
| B | `eq:capacity`, operational capacity equals the regularized supremum | Existing qualified finding retained. The exported root states the supremum identity; the limit identity is separately proved. |
| C | Small positive one-use information, unbounded operational gain and two-use ratio | Coverage qualification corrected below. The root does not assert the absolute two-use separation or sequence limits. |
| D | `eq:chi-extension` at every positive tensor power | Existing qualified finding retained, including channel-label representation and minimum-entropy/attainment distinctions. |
| E, two roots | `rem:separation-cost`, one-use bounds and two-use input-cost lower bound | Both existing qualified findings retained, including eventual total-family completion and the separate operational lower bound. |
| F | `cor:separation`, `eq:small-large` | Source-supported strengthening of the finite existential absolute-separation endpoint, through the alternate deterministic construction. |

The unchanged definitions use actual finite Kraus CPTP channels, complex
density matrices and finite output ensembles, base-two Holevo information,
and the physical tensor-product channel. In particular, `chiTwo` allows
entangled inputs across the two channel uses. The definitions are unchanged
from the source-first historical reviews; no new definition-equivalence claim
is inferred merely from a theorem's name.

### C: explicit correction of historical coverage

The earlier review described C as a stronger common-witness conjunction of
the two source corollaries. That description overstates its coverage.
Its conclusion gives `0 < chi ≤ ε`, large operational gain, and a large
two-use ratio. It does not imply `R ≤ chiTwo / 2`: the proved relation is
`chiTwo / 2 ≤ capacity`, which cannot transfer a capacity lower bound in
that direction. The old review manifests and reports retain their exact bytes;
the successor records this correction explicitly.

C imports `OperationalCodingTheorem`, sharing proved dependencies with B.
Lean replay and Nanoda check the solution export's dependency closure.
Shared proof dependencies do not constitute an unchecked coding assumption.
Review of the challenge's expected definitions and import closure remains
separate from checking the solution proofs.

### F: absolute two-use separation

The arXiv statement `eq:small-large` assumes positive real `ε` and `R`,
and asks for a channel with `chi ≤ ε` and `R ≤ chiTwo / 2`.
[DeterministicConsequences.actual_small_large](../Nonadditivity/DeterministicConsequences.lean)
has the explicit type

```lean
theorem actual_small_large {ε R : ℝ} (hε : 0 < ε) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ ε ∧ R ≤ T.chiTwo / 2
```

The theorem permits any real `R` and gives positive `chi`, so it implies the
displayed manuscript existential clause. Its witness comes from the existing
deterministic finite-moment/damped separating family. It does not assert the
manuscript's prescribed Haar dimensions, export the named sequence-convergence
theorems, or include an operational-capacity conjunct. Those are separate
proved endpoints. F imports `ActualConsequences` to define its objects and
does not import its solution module `DeterministicConsequences`.

## Published wording and proof-encoding qualifications

The v2 abstract says the certificate is “for our proofs,” and the AI-usage
paragraph refers broadly to autoformalized results and proofs. This continuation
does not adopt a full-manuscript or proof-by-proof coverage claim. In particular,
the general undamped norm certificate for every `κ > 1` and all sufficiently
large dimensions, general Haar strong-convergence interfaces, and the
distinct-channel Weyl identity remain outside the completed scope.

The v2 exploration-mark paragraph records a run of tree steps and the source
label of the step ending that run. The formal `HaarPathMarks.explorationMark`
uses the endpoint before the first fresh traversal and the source color of
the next traversal. `HaarPathExplorationBlocks`, `HaarPathReconstructionTree`,
and `HaarPathReconstructionFresh` prove reconstruction for that explicit
old-tree/fresh-run encoding. The changed v2 prose is not a literal restatement
of that definition; an equivalence of the two proof encodings is not asserted
or proved here. The endpoint statements and existing formal proof remain
unchanged.

## Mechanical evidence

The successor manifest binds this report, the reviewed source delta, exact
source inputs, and fresh local expected-type applications and seven root
type/axiom closures. Its mechanical scope is incremental and distinct from
the separately selected portable full-build, Comparator/Lean replay, and
Nanoda records. A retained status is valid only when its bound commands
actually succeeded; this prose does not substitute for those records.

Reproduce the selected full suite with:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/additive-20261008/source-certificate.json
```

Then check the selected evidence with `verification/check_reports.py` and
`verification/check_statement_audit.py`. These freshness validators check
recorded scope and hashes; they do not independently redo semantic review.
