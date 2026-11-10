# Additional worked-example compilation — 10 November 2026

Five commented Lean walkthroughs compiled successfully on Lean 4.32.0, with **zero errors and zero warnings**. Their **38 printed theorem reports** use only `propext`, `Classical.choice` and `Quot.sound`. The unchanged OPE dependency modules also compiled; their five printed theorem reports use only the same permitted axioms.

| Assessment entry | Example | Audited example theorems |
|---|---|---:|
| A1 | [OSAxioms-20261028.lean](../../../docs/examples/OSAxioms-20261028.lean) | 9 |
| A2 | [OperatorContent-20261028.lean](../../../docs/examples/OperatorContent-20261028.lean) | 7 |
| A3, A5 | [LatticeAndScale-20261028.lean](../../../docs/examples/LatticeAndScale-20261028.lean) | 11 |
| A6 | [TranslationWard-20261028.lean](../../../docs/examples/TranslationWard-20261028.lean) | 4 |
| A8 | [CommonOPE-20261028.lean](../../../docs/examples/CommonOPE-20261028.lean) | 7 |

The labels match the current assessment draft. The [initial record](../result.json) separately covers OctoberChain and LeadingTrace, bringing the maintained collection to seven examples. The assessment itself was not edited.

The [machine-readable record](result.json) contains the exact commands, source and log hashes, compiler version, source comparisons and axiom reports. The adjacent logs cover the five examples and the two OPE dependencies. The final example sources contain no `axiom`, `unsafe`, `sorry` or `admit` tokens outside comments.

These checks reused the existing October acceptance build. All 9,477 submitted Lean source files and the 41 review modules present in that environment matched the packaged sources byte for byte. `OPESpec.lean` and `OPECheck.lean` were absent from that environment and were compiled from the unchanged packaged copies into a temporary object directory. No imported compiled objects were independently re-audited by this step.

This is supplementary ordinary Lean compilation, not a new Comparator run or a fresh whole-submission rebuild. The examples explain existing results and expose consequences; they do not modify the review specifications or historical verification evidence. Axiom reports constrain proof dependencies but do not establish that the prose accurately interprets every definition: that remains a human review task.

Use the [portable compilation instructions](../../../docs/examples/README.md) to reproduce the examples. Absolute paths in the record describe this local run; they are not required paths on another machine. Compiled objects and dependency caches are not included.
