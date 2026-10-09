# Release preparation and remaining review

This repository publishes the completed principal Lean results and their verification evidence. The full manuscript is not formalized. Complete the publication checks below against a frozen release candidate; do not replace an earlier record's source hashes with those of changed sources.

## Current arXiv v2 and added-root candidate

The current manuscript preserves the exact upstream arXiv v2 source. The
current suite contains six configurations and seven theorem roots, including
the absolute two-use separation root `actual_small_large`. The
[verification index](../verification/README.md) identifies the selected portable
record and additive source certificate, and the [v2 statement review](STATEMENT_AUDIT_V2.md)
records the qualified correspondence. The current full proof execution and
freshness checks passed, with their original input bindings retained under
`verification/portable-20261008/`. The separate v2 review includes observed
seven-root type and axiom checks under `verification/statement-audit-20261008/`.
Rebuild and check the reader site from these selected records before publication.
The checklist below records the earlier release.

## Historical v1.0.0 publication checks

- [x] Run `bash scripts/verify.sh all --source-certificate verification/elaboration-20261006/source-certificate.json` successfully on the candidate. Retain its fresh Lean build/audit, Comparator/Lean replay, Nanoda source/build receipt, controls, and complete logs under `verification/portable-20261007`. Record the actual source commit and hashes; challenge compilation alone does not establish Comparator or Nanoda success.
- [x] Select those portable records explicitly in `metadata/results.json` and run `python3 verification/check_reports.py`. Preserve the October 2 portable evidence and its original bindings.
- [x] Finish the [cleanup statement-review continuation](STATEMENT_AUDIT_DELTA.md), record its actual current-source exact-type and axiom checks, and select its manifest. Run `python3 verification/check_statement_audit.py`; preserve the parent reviews and their qualifications. This is an AI source review, not human review or machine-certified English–Lean equivalence.
- [x] Run the checker controls, release metadata/reference validation, and fresh declaration export comparison required by the candidate. Keep the explicit certificate option for Lean and `all`; the validator's default remains the historical source gate.
- [x] Rebuild the offline browser with `python3 tools/docs-site/build.py`, then run `python3 tools/docs-site/build.py --check`. Confirm its downloadable sources, verification commands, selected evidence and statement-review links describe the checked candidate.

The [v1.0.0 GitHub release](https://github.com/JWang226/Holevo-Additivity-Gap/releases/tag/v1.0.0) is the publication record for the verified packaged commit, tag and notes. Release claims retain the pinned Mathlib cache, unsandboxed Comparator/Nanoda execution and formalization limits.

The all-mode proof verification and fresh declaration export passed on source commit `38b36070`. The following recorder failed on universe-decorated axiom names; its [failed execution record](../verification/github-actions-release-all-38b36070.json) is preserved. The [recovery receipt](../verification/statement-audit-20261007/recovery.json) binds the original successful Linux statement commands and root-probe output to the completed continuation. No proof commands were rerun during recovery.

The [cleanup certificate](../verification/elaboration-20261006/source-certificate.json) records the completed rebuild and exact public-type comparison. It does not supply a new Comparator, Nanoda or manuscript-correspondence result. The [verification index](../verification/README.md) identifies each check's scope and retained evidence.

## Attribution and future review

- The revised manuscript incorporates both counting repairs; its hash and
  correspondence metadata are updated together. Keep them synchronized with
  any future manuscript revision.
- Confirm named contributors, author details, and how AI assistance should be
  acknowledged. License selection for original code and manuscript material
  remains pending; preserve the existing copyright, third-party attribution
  and license until the authors make that selection.
- Review the natural-language/formal correspondence, including shared
  definitions in the challenge environments, and document any human review.
- Cite the actual GitHub release tag or commit alongside the repository URL.
  Do not invent a DOI or a scholarly publication record.
- Include any available original prompt transcripts, model identifiers, and
  measured compute costs. Keep genuinely unavailable values marked unknown.
- If the work is announced as a paper, arrange an appropriate scholarly deposit
  separately from the GitHub code release.

Repository preparation does not itself establish human understanding or peer
review. The [formalization status](FORMALIZATION_STATUS.md) should accompany
announcements, including its explicit limits.

The default integrity check enforces the historical audited proof-source
baseline. The current explicit additive certificate preserves the completed
cleanup rebuild/type evidence and binds the added challenge configuration;
it does not itself record fresh proof execution.
Future mathematical changes require fresh verification and a reviewed successor
record with its own source bindings. Keep previous evidence available; new
source hashes alone do not establish that changed proofs have been checked.
