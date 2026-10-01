# Holevo Additivity Gap

Lean 4 certificates accompanying the manuscript by Jinzhao Wang. The principal
channel constructions, quantitative dimension bounds, operational capacity
consequences, and input-cost asymptotics are proved with no project-specific
axioms or unfinished proofs in the proof library.

**The full manuscript is not formalized.** Two intermediate counting arguments have been
repaired in Lean; the included manuscript is the unchanged source version.
See [formalization status](docs/FORMALIZATION_STATUS.md) and
[corrections](docs/CORRECTIONS.md) for the precise scope.

## Results and artifacts

| Artifact | Purpose |
| --- | --- |
| [paper/nonadditivity.tex](paper/nonadditivity.tex) | Original manuscript, with embedded bibliography |
| [Nonadditivity/](Nonadditivity/) | Modular Lean proofs and definitions |
| [All.lean](All.lean) | Single build entry point, including the axiom audit |
| [formalization.yaml](formalization.yaml) | Project metadata and principal formal declarations |
| [metadata/results.json](metadata/results.json) | Manuscript-label-to-Lean correspondence, including limitations |
| [ComparatorChallenges/](ComparatorChallenges/) | Separate expected theorem statements and Comparator configurations |
| [verification/](verification/) | Audit evidence and release verification records |
| [docs/PROOF_MAP.md](docs/PROOF_MAP.md) | Detailed proof architecture |
| [docs/AI_USAGE.md](docs/AI_USAGE.md) | AI assistance and available provenance |

The main endpoints construct actual finite-dimensional CPTP channels. Classical
capacity is defined through physical codes and vanishing decoding error, then
proved equal to regularized Holevo information. The claims concern the gap
between single-use Holevo information and multi-use information or capacity;
they do not assert nonadditivity of operational capacity across distinct channels.

## Build and check

With [elan](https://github.com/leanprover/elan) installed, these commands download
the pinned Lean `4.29.0-rc6` dependencies and check the proof library and its
transitive axiom audit:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git
cd Holevo-Additivity-Gap
lake exe cache get
lake build All
```

For a full project-source rebuild with a retained audit log:

```sh
./check.sh
```

This compiles every proof module and checks all transitive dependencies of every
project declaration. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. The audit covers definitions with proof fields and private helpers,
as well as theorem constants. It does not establish that an informal statement
has been translated correctly; the correspondence catalog supports that review.

To validate metadata, source provenance, and declaration references:

```sh
python3 -m pip install -r requirements-validation.txt
python3 scripts/validate_release.py
```

The validator invokes the Lean declaration check. For metadata and source
integrity checks before a build, use `--static-only`.

Comparator separately checks the six expected theorem statements in five
configurations against the solution proofs. On Linux, install a working
[landrun](https://github.com/Zouuup/landrun) from its upstream source and use a
nonprivileged account with a working systemd user session. From the project root,
build the matching Comparator and `lean4export`, preserving its committed manifest:

```sh
git clone https://github.com/leanprover/comparator.git ../holevo-comparator
git -C ../holevo-comparator checkout a4f696825c583ed8a5b4060d9a0faa5b882d365b
(cd ../holevo-comparator && lake build comparator lean4export)
export NONADDITIVITY_COMPARATOR_BIN="$(cd ../holevo-comparator && pwd)/.lake/build/bin/comparator"
export PATH="$(cd ../holevo-comparator && pwd)/.lake/packages/lean4export/.lake/build/bin:$PATH"
systemd-run --user --pty --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" -E PATH="$PATH" \
  -E NONADDITIVITY_COMPARATOR_BIN="$NONADDITIVITY_COMPARATOR_BIN" -- \
  bash -c 'set -e; for config in ComparatorChallenges/*.json; do lake env "$NONADDITIVITY_COMPARATOR_BIN" "$config"; done'
```

**An end-to-end Comparator run has not been performed.** Challenge elaboration
and local statement checks passed; they are separate from Comparator verification.
The expected-statement files contain six deliberate placeholders and are excluded
from the proof build. The solution library contains none. See the
[detailed instructions and trust assumptions](ComparatorChallenges/README.md)
for tool revisions, individual checks, and verification scope.

## Verification status

The retained baseline audit checked 368 modules, 9,107 project declarations, and
7,219 theorem constants, with only the three standard axioms above. That run
used verified cached objects and rebuilt changed dependencies; it was not a
clean rebuild. The release organization adds copyright comments, metadata,
documentation, an aggregate entry point, and isolated challenges. The release
checks distinguish unchanged proof bodies from newly compiled entry points.
See [verification/README.md](verification/README.md) for evidence and limits.

## Attribution and licensing

The layout follows the public [ten-proofs](https://github.com/openai/ten-proofs)
repository and the formalization recommendations in
[AGM's September 29, 2026 guidance](https://agmai.org/general-sep29/).
This project is not presented as an OpenAI-authored paper or official lab release.

Original project material has no blanket open-source license selected yet.
Copyright notices and existing third-party licenses are preserved; see
[COPYRIGHT.md](COPYRIGHT.md) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
[RELEASE_CHECKLIST.md](docs/RELEASE_CHECKLIST.md) records the remaining publication
decisions and checks, including manuscript corrections, author details, licensing,
and a full Comparator run.
