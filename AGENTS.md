# Proof maintenance

The production proof build contains `Nonadditivity/`, `Nonadditivity.lean`,
`Audit.lean` and `All.lean`. `./build.sh` recompiles all own modules serially;
`./check.sh` retains its complete axiom-audit log. Challenge placeholders and
scratch diagnostic probes are outside this proof build. Preserve copyright and
attribution headers. Do not edit archived sources under `sources/`.

For cleanup, preserve public names, declaration roles, hypotheses and canonical
kernel types. A textual unused-name search is insufficient: inspect exported
expression consumers, registered instances and generated helpers before deleting
private declarations. Keep deliberate facade re-exports and the dedicated audit.

For elaboration measurements, use `scripts/elaboration_test.py` and
`docs/ELABORATION_CLEANUP.md`. Preserve populated dependency objects; do not run
`lake clean`, `lake update`, or rebuild upstream sources as part of a timed run.
Do not run concurrent measurements against the same own artifact tree. Inspect
actual source/artifact guard failures; process presence alone is informational.

The measured reindexing improvement pins `Equiv.summable_iff`'s function before
inference. Its saving is tactic execution, with essentially unchanged typeclass
inference. Do not spread class caches from name-count tables: identify the actual
closed instance goal, place a cache outside section-variable scopes, and A/B it.
The spectral ascription trial was null; the Gram helper trial failed under the
existing heartbeat limit. Keep failed/null trials and revert unsupported edits.
Do not raise heartbeat or recursion limits to label a candidate successful.

Require a >=2 second or >=10% relevant-phase improvement with unchanged public
statements and no material transferred regression; use at least three pairs for
wall-time claims. Two full builds are descriptive rather than causal attribution.
Record legacy `module`-header limitations rather than silently migrating exports.

A new Lean rebuild/type certificate is explicitly narrower than Comparator,
Nanoda, or manuscript correspondence. Preserve historical evidence and its source
bindings; never reseal it against changed sources. `--source-certificate` selects
current cleanup evidence explicitly; the validator's default remains historical.
