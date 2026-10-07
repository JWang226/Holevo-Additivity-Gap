# Same-runner elaboration measurement

The workflow is `.github/workflows/elaboration.yml`; its harness and fixed
continuation helper are in `scripts/`. The workflow definition can be on `main`;
the dispatched baseline must contain both scripts. Select an immutable full SHA
for an exact repeat. A later cleanup publication commit is a different snapshot.

The job uses Ubuntu 22.04, the repository's pinned Lean/cache setup, GNU time,
and one serial build driver. Setup is outside timing. Baseline, A/B trials,
after, and declaration export use the same runner and compiled dependency cache.
Neither `lake clean`, `lake update`, nor upstream compilation is requested.
No Landrun is used. These measurements do not claim Comparator or Nanoda results.

Dispatch explicitly (replace the branch names):

```sh
gh workflow run elaboration.yml --repo JWang226/Holevo-Additivity-Gap --ref main \
  -f baseline_ref=743cc95bc4c0b1bca891994def26d9e5f8c7aad6 \
  -f after_ref=YOUR_CANDIDATE_BRANCH \
  -f control_ref=YOUR_FRESH_CONTROL_BRANCH
```

Use a fresh control branch starting at sequence 1; the historical control
branch is already at sequence 4. The candidate branch must descend from the
selected baseline and remain limited to permitted proof-source changes.

Read the uploaded `elaboration-before` artifact. Its `summary.json` identifies
the measured full baseline SHA, coverage, per-file timings, and eight warm phase
profiles. The two-hour continuation deadline starts after this upload. There are
six request slots; a final request may use any slot and skips remaining slots.
Use at most five trial requests before the final request.

The public control branch contains `elaboration-request.json`. Commit and push
exactly one of these request shapes. Sequences start at 1 and increase by one
after every accepted request, including failed/rejected trials. A stale sequence
is ignored while the job waits. No request accepts a shell command.

For a measured intervention:

```json
{
  "schema_version": 1,
  "sequence": 1,
  "mode": "profile",
  "baseline_sha": "REPLACE_WITH_COMPLETE_40_CHARACTER_BASELINE_SHA",
  "candidate_sha": "REPLACE_WITH_COMPLETE_40_CHARACTER_CANDIDATE_SHA",
  "modules": ["Nonadditivity.Example"],
  "repetitions": 3
}
```

Push the candidate commit to the explicit `after_ref` source branch before the
request. The candidate must descend from the measured baseline and may change
only existing, regular own Lean source files. Changes to compiler drivers,
dependency pins, scripts, configuration, metadata, symlinks, and file additions
or deletions are rejected. List all changed modules among the 1–10 requested
modules. A requested module cannot transitively import another changed module:
such a profile would otherwise use an old dependency artifact. Independent
module interventions and several successive variants of a single module work.
For separate module trials, starting each candidate from the measured baseline
is simplest. Cumulative changes are permitted only when this dependency guard
passes.

Each request runs baseline/candidate, candidate/baseline, baseline/candidate,
with one serial no-output `--profile` run per requested module in each half.
Raw logs, GNU time output, source hashes, phase totals, and median CPU/wall/phase
comparisons are uploaded immediately as `elaboration-request-N`. Failed
candidates are recorded and do not abort continuation. The helper returns the
checkout to the measured baseline. Existing own artifacts and all upstream
artifacts must remain unchanged throughout these profiles.

For final selection, push the retained source tree to `after_ref`, then request:

```json
{
  "schema_version": 1,
  "sequence": 2,
  "mode": "final",
  "baseline_sha": "REPLACE_WITH_COMPLETE_40_CHARACTER_BASELINE_SHA",
  "after_sha": "REPLACE_WITH_COMPLETE_40_CHARACTER_AFTER_SHA"
}
```

The final SHA must exactly match that source branch's current head. Zero net
proof edits are allowed, including selecting the original baseline SHA after
reverting all null or regressing trials. The final snapshot runs the unchanged
full harness with `--prior-summary` pointing to the uploaded baseline. It
independently profiles its own worst eight modules; supplemental profiles cover
every baseline worst-eight module and edited module missing from that list.
Those supplemental results are separate from the original full after summary.

Only after all measurements, `python scripts/export_declarations.py --fresh`
exports the types from the freshly compiled after objects. The
`elaboration-after-declarations` artifact contains `metadata/declarations.json`
and selected exporter logs/checkpoints when hidden-file upload is enabled.
The historical run used the older workflow definition; its artifact inventory
and preserved export identify the files actually retained. Use decoded canonical
kernel types to compare
the public API against the original reviewed export; generated proof helpers
may change. The exporter is not a proof rebuild or an independent kernel check.

The final `elaboration-after-and-continuation` artifact preserves all evidence,
including setup/failure records and the original before/after reports. GitHub
artifacts expire after 30 days: download and store selected evidence in the
repository before publishing detailed reports.

The helper is copied outside the checkout before measurement. It fetches only
the fixed public repository over credential-free HTTPS, never prints tokens,
and uses exactly the same committed harness implementation for every candidate.
Process visibility is informational; source/artifact mutations invalidate
measurements. Warm page caches and ordinary runner scheduling can still add
noise, so interpret three-run phase/CPU comparisons alongside wall time.
