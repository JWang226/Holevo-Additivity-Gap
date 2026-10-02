# AI assistance and provenance

The project formalizes *Unbounded Holevo additivity gaps in finite dimensions*,
whose supplied manuscript identifies Jinzhao Wang as author. The manuscript was
provided in the working session; this record does not reconstruct its earlier
authorship or research history.

OpenAI Codex assisted with developing Lean definitions and proofs, investigating
failed counting estimates, compiling and auditing the formalization, and
organizing the release artifacts. Several AI agents worked on separate proof
components and reviews. This is a description of assistance, not a claim that
OpenAI is an author or copyright holder of the paper.

## Available instructions and work record

The available conversation includes requests to continue proving the remaining
results, including “prove the rest” and “keep trying harder.” The release
organization was requested on October 1, 2026 UTC, with instructions to follow
the `openai/ten-proofs` layout and AGM's September 29 formalization guidance,
in preparation for a later GitHub push.

These excerpts are not a complete prompt transcript. Earlier prompts, complete
model invocation records, and initial unedited outputs are not part of this
repository. They have not been reconstructed or invented.

## Technical work summary

The formalization uses actual finite Kraus channels, density matrices, entropy,
and coding protocols. It develops deterministic and Haar-based channel
constructions, a finite-dimensional operational coding theorem, Weyl-extension
identities, operator factorization, and quantitative dimension asymptotics.
Concrete finite paths exposed two invalid intermediate counting steps. New
counting estimates were proved and connected to the required moment bound.
The principal results do not assume the broader Haar-convergence predicates
that remain unproved elsewhere in the library.

The compiler checked the proofs; a separate project audit collected their
transitive axioms. The correspondence metadata and separate challenge statements
make the relationship to the manuscript inspectable. Formal checking does not
replace human review of definitions, hypotheses, correspondence, or exposition.

## Recorded and missing provenance

| Field | Record |
| --- | --- |
| Assistant framework | OpenAI Codex |
| Model attribution in the revised manuscript | GPT-6 Astra, reported by the author |
| Exact runtime identifiers for the full proof-development history | Not recorded in the retained artifacts |
| Full prompts and raw model outputs | Not retained in this repository |
| Total elapsed research time | Not measured; audit timestamps are available |
| Compute usage and monetary cost | Not recorded |
| Automated proof verification | Lean compilation and transitive axiom audit; see `verification/` |
| Comparator execution | See the current challenge README and release verification record; do not infer execution from prepared configurations |
| AI review | Conducted during development and release preparation |
| Independent human mathematical review | Not documented in the available record |
| Other attempted problems or failed experiments outside this project | Not recorded |

The revised manuscript supplies the author's model attribution. Complete
runtime invocation records are still unavailable. Its verification sentence
is limited to the principal Lean endpoints and recorded build/audit success;
Comparator execution remains pending. The missing fields remain explicit so
that future maintainers can add actual records. No claim of complete compliance with every AGM recommendation is made.
