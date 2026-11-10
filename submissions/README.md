# Submission packages

Each directory holds the original material and the review of one dated submission. The current package is [OpenAI, 28 October 2026](openai-20261028/README.md).

Use a stable directory name such as `openai-20261028` or `author-YYYYMMDD`. Use the date that identifies the submission, and document any distinction between that date and its receipt or import date. A later submission gets a separate directory even when it shares much of its source with an earlier one.

| Directory within a package | Purpose |
|---|---|
| `submission/` | The original submitted distribution, kept unchanged |
| `checks/` | The group's formal statements, bridge lemmas and proofs |
| `verification/` | Reference targets, configurations, tool versions and controls |
| `scripts/` | Commands for reproducing the checks |
| `evidence/` | Dated results, logs and descriptions of their scope |
| `provenance/` | Source revisions, hashes, upstream definitions and licenses |
| `docs/` | The submission's explanations, examples and rerun guide |

Every package should identify the exact inputs used for each verification result. Preserve historical records when the review is extended. If a submitted source needs a correction, record it explicitly as a patch or separately identified revised tree, together with its own verification evidence; do not overwrite the original source.

Each package must contain the source and review inputs needed for its checks. Public tool and library dependencies may be fetched at pinned revisions. An original-submission repository provides an additional provenance reference, but should not be a required private dependency of a released package.

The top-level [documentation](../docs/README.md) indexes assessments and examples across submissions. Assessment PDFs use stable top-level paths such as `docs/assessment-1.pdf`. Other submission-specific documents are stored inside their packages; indexes link to them rather than maintaining competing copies. Shared explanations and comparisons also belong in the top-level `docs/` directory.

Submission proposals and the group's review discretion are described in [the main README](../README.md#making-a-submission).
