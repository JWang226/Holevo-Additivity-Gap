# Further review and verification

This repository publishes the completed Lean results and their verification evidence.
This file records remaining attribution, correspondence-review, and independent-verification work.

- The revised manuscript incorporates both counting repairs; its hash and
  correspondence metadata are updated together. Keep them synchronized with
  any future manuscript revision.
- Confirm named contributors, author details, and how AI assistance should be
  acknowledged. Select licenses for original code and manuscript material;
  preserve the existing third-party attribution and license.
- The full project-source rebuild and audit passed in GitHub Actions on
  `5345459` (run `36956367986`, attempt 1); see
  [the execution record](../verification/github-actions-5345459.json).
  Keep future commit checks and their cache/rebuild boundaries documented.
- Run the Comparator configurations using the documented compatible toolchain
  and independent checker. Record tool revisions and actual results. Challenge
  compilation alone does not satisfy this step.
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

The current integrity check intentionally enforces the audited proof-source
baseline. Future mathematical changes require a fresh build and audit, a new
verification record, and an explicit update of that baseline comparison. Keep
the previous evidence available in version history; do not treat new source
hashes alone as evidence that changed proofs have been checked.
