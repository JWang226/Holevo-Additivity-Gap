# Reader-site generator

Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See `COPYRIGHT.md` for licensing and attribution.

From the repository root, with Python 3:

```sh
python3 tools/docs-site/build.py
python3 tools/docs-site/build.py --check
```

The standard-library generator writes the self-contained `html/` directory.
Open `html/index.html` directly or deploy that directory as a static site.
Assets and search data are local; browsing works offline without a server.

The mathematical reader has six chapters, ten concept pages, explanations of
all 25 result records, and seven proof-stage explanations. Its handwritten
Markdown lives in `tools/docs-site/reader/`; `reader/index.json` registers the
pages and their summaries. Result IDs match `metadata/results.json`, whose
formalization statuses and scope notes are retained unchanged. Edit these
sources, then run both commands above.

`correspondence.html` connects manuscript statements and argument locations to
informal guides and exact Lean declarations in four columns. Edit the selected
passages in `correspondence.json`; the generator validates their LaTeX labels
against the included revised manuscript and creates a source browser with line
anchors. Status and scope come from `metadata/results.json`. The map supports
local search and status filters, remains readable without JavaScript, and has a
downloadable `correspondence-map.json` with source hashes and all link targets.

The six challenge roots also have independent AI source-semantics reviews in
`docs/STATEMENT_AUDIT.md` and its linked reports. Relevant correspondence rows and
result pages display report links and recorded verdicts. The downloadable map
retains each reviewed declaration, report, verdict, and qualification, plus the
source URL and hash of `verification/statement-audit.json`. These reviews do not
machine-certify English–Lean equivalence.

Every build validates the audit's source, report, and mechanical-evidence hashes
before displaying it. Exact downloads include the manifest, reports, freshness
checker, negative controls, logs, and mechanical probe. Existing proof-source
downloads are reused. To check only the recorded audit's freshness:

```sh
python3 verification/check_statement_audit.py
```

This checks hashes, references, and recorded provenance; it does not redo the
semantic review or run proof checks. Its mechanical record covers incremental
exact-type applications and axiom checks with existing compiled dependencies.
The Verify page retains separate Lean, Comparator, and Nanoda reproducers.

Use `$...$` for inline mathematics and a separate pair of `$$` lines for
display mathematics. KaTeX 0.19.0, its fonts, and its original MIT license are
bundled in `vendor/katex/`; no CDN, npm installation, or Node build is needed.
The Markdown renderer supports headings, paragraphs, lists, tables, links,
and fenced code. Links to mathematical and formal pages use these targets:

| Target | Destination |
| --- | --- |
| `lean:Nonadditivity.Namespace.declaration` | Exact exported declaration |
| `guide:introduction` | Registered reading chapter |
| `concept:channels` | Registered concept page |
| `result:prescribed-dimensions` | Result explanation and formal correspondence |
| `stage:1` | Explanatory section of the proof route |
| `site:verify.html` | Other generated page or artifact |

Every attached Lean name must exist in the actual declaration export. The
generated `html/reader-map.json` records explanation sources and SHA-256 hashes,
declaration kinds, and exact page targets. Declaration pages link back to their
explanations, and proof-map details link to the relevant mathematical page.
These are reading correspondences; they do not certify equivalence between
English prose and proof terms. Search includes the mathematical explanations
and prioritizes relevant concept and result titles while preserving exact Lean
name matches.

The site includes all 366 proof modules and three aggregate entry points,
all 25 correspondence records and their
49 exact declaration references, every exported project constant with its full
elaborated Lean type, full source downloads and line anchors,
direct imports and reverse imports, a reading route, verification commands,
scope limits, and rendered repository documents. Search indexes every exported
constant, all module names, result names, and manuscript labels. The filter
uses Lean’s exported `Name.isInternal`, `Name.isInternalDetail` and
`isPrivateName` predicates; each declaration page names the flags it has.
Those predicates do not identify every compiler-generated helper.

Result pages retain conservatively quoted literal source headers, with their
ambient context distinguished from the complete elaborated type on each
declaration page. Types and direct constant references are exported from the
actual Lean environment in `metadata/declarations.json`; they are never
inferred from the source text. Every kernel-relevant field of each type is
preserved as a shared expression DAG: all arguments, universes, binders and
name components are retained; kernel-irrelevant metadata annotations are
omitted. The canonical UTF-8 JSON is stored losslessly as gzip/base64 with
its byte count and SHA-256. It is a machine expression representation, not
Lean source text. Each page provides the readable Lean printer view, a lazily
decoded JSON preview capped at 64,000 characters, and the complete
`.expr.json.gz` download. Browsers with `DecompressionStream` can also
download the complete decoded `.expr.json`; compressed downloads remain
available without it. Regenerate that export using the procedure in
`verification/README.md` when proof sources change, then rebuild these pages.
The generator refuses stale SHA-256 export provenance before generating.

Declaration pages list constants appearing directly in the type and stored
proof or definition, plus reverse project references. The dependency explorer
starts with four mathematical proof maps: the prescribed
channel, the separate sharp Haar bound, operational capacity gain, and input-qubit
cost. `proof-graph.json` supplies reviewed labels, statements, and scope. The
generator derives every arrow from an actual path through stored proof/definition
references, stops at other displayed results, and removes redundant arrows.
Every selected step must have a path to its preset endpoint or the build fails.
The diagram points from ingredients to conclusions; its supporting Lean paths
remain inspectable. The main channel uses the stronger `2^80 p^80` moment route;
the separate sharp endpoint restores `2^32 p^80`.

The detailed Lean-reference view retains all project declarations, direct type
and proof/definition references, reverse traversal, name/result search, and
complete paginated neighbor lists. Displayed branches prioritize described
mathematical results and ordinary theorems. Lean-flagged helpers can be included
explicitly. Readable statements and precise source links remain available.
These edges are syntactic references, with no minimality or informal-proof
equivalence certificate asserted. Imported library
constants remain plain names unless their precise documentation target is
available. Module imports and the English proof route remain distinct.

`--check` compares generated bytes and checks local links, HTML anchors,
search targets, exact source downloads, export source hashes, and project
reference consistency. Kernel type artifacts are stream-checked one record at a
time for UTF-8, byte count and SHA-256, then validated for well-formed DAG
node tags, backward child references, universe/name references and binder
information. It does not
check any proof or independently certify
the committed declaration export.
`html/generation.json` records the input hashes and counts. Generated content
contains no local absolute paths or timestamps, so it is deterministic.

The generator owns `html/`: files in that directory not generated by it are
removed during a normal rebuild. Keep handwritten source in `tools/docs-site/`.
