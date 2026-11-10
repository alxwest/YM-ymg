# Verification evidence

The later [initial commented-example compilation](examples-2026-11-10/README.md) covers OctoberChain and LeadingTrace. The [additional example compilation](examples-2026-11-10/additional/README.md) covers five further walkthroughs for the assessment’s A1–A8 topics. These are supplementary Lean compilations, separate from the historical Comparator endpoints below.

Historical evidence is copied from the earlier review, without rewriting its logs or changing its dates. Paths in those records describe the machine and directories used at the time; they are not dependencies of the new runner. Some older records say a later check had not yet been run. The table below distinguishes the checks chronologically.

| Evidence | Result and scope |
|---|---|
| [October source build](historical/build/rebuild-results.json) | Passed on 29 October 2026 using Lean 4.32.0 on macOS arm64. The project was built locally from an initially absent project build directory, using the pinned Mathlib cache. [Warnings](historical/build/warning-summary.json): 2,453. |
| [Submitted endpoint Comparator](historical/submission-comparator/result.json) | Passed on 30 October 2026 for `YangMills.jointExistence`, with standard permitted axioms. |
| [Combined review build](historical/acceptance-build/validation.json) | 41 review modules compiled, zero warnings, eight audited declarations using standard axioms only. Reused the submitted project's build. |
| [Combined endpoint Comparator](historical/acceptance-comparator/result.json) | Passed on 3 November 2026 for `YMReview.Acceptance.combined_acceptance`, frozen at review commit `1dec9fa5d3ab19794d082573bc885709ec68aa3a`. Four controls behaved as expected. |
| [OPE adapter build](historical/ope-build/validation.json) | Two additional modules compiled on 3 November 2026, with zero warnings and five audited declarations using standard axioms only. This record is not a Comparator run. |
| [OS source correspondence](historical/os-correspondence/provenance.json) | Four whole declarations compared after documented normalization; copied and excerpted analytic sources identified. The portable runner repeats the four-declaration comparison. |

The historical Comparator checks used pinned upstream tools in macOS development mode, without Linux/Landrun isolation or an external kernel. The combined run reused the previous source build and compiled its own review project. Its source snapshot records a pre-existing change to three line-number fields in `verification/declaration-usage.tsv`; mathematical source files matched the original distribution and remained unchanged during the run. The `submission/` copy in this repository restores and preserves the exact original report too.

## Release-package replay on 5 November 2026

The [new replay summary](release-2026-11-05/summary.json) records a successful packaged build, fresh compilation of all 43 review modules with zero warnings, the 13 required endpoint audits and 96 axiom reports in total, the four OS declaration comparisons, and the four Comparator controls. Every reported axiom is one of the three permitted standard axioms.

The [OPE Comparator run](release-2026-11-05/ope-comparator/result.json) also passed for `YMReview.OPE.constructed`. This extends the earlier evidence with a separate check of the OPE adapter; it does not retroactively expand the scope of the earlier combined theorem. The pinned tools were independently fetched and built using the new runner, and their binaries matched those used for the OPE run.

The packaged source build reused the verified October build cache. Our 43 review modules were compiled into a fresh directory. These are different forms of reuse and are recorded separately. The source files remain byte-identical to the imported distribution and review snapshots. The OPE and tool-bootstrap directories retain the version of the runner used for those checks; the final runner also includes the validated diagnostic-aggregation fix and input-manifest checks.

Selected logs and command records are included under [release-2026-11-05/](release-2026-11-05/). No `.olean` files, dependency caches, tool binaries or temporary proof exports are committed. Final human assessment remains pending.

The archived distribution contains 9,508 files, including its own checksum manifest. Its archive hash and import hashes are in [provenance/october-import.json](../provenance/october-import.json). The local archive was obtained on 28 October 2026; the date on which OpenAI originally sent it is not confirmed by this record.

