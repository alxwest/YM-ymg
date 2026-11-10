# Reading the results and checks

Start with the [assessment of the October submission](assessment-1.pdf). Part I explains the construction and its mathematical claims; Part II explains verification, validation and the independent checks. The [assessment index](assessments/README.md) identifies the document.

For a reader familiar with Yang–Mills theory and Lean, the following route connects the assessment to the formal statements and their evidence:

1. Read [the check scope](../submissions/openai-20261028/docs/checks.md), then [AcceptanceSpec.lean](../submissions/openai-20261028/checks/AcceptanceSpec.lean). Start with `CombinedAcceptance`, `Accepted` and their component structures. The quantifiers specify which construction data must satisfy the clauses together.
2. Inspect the submission's [Spec.Final](../submissions/openai-20261028/submission/YM/Spec/Closed.lean), then [CombinedAcceptance.lean](../submissions/openai-20261028/checks/CombinedAcceptance.lean). The [commented Lean examples](examples/README.md) follow individual claims through their definitions and proofs, including the lattice-to-continuum chain.
3. For the independent OS comparison, read [CompleteOS.lean](../submissions/openai-20261028/checks/CompleteOS.lean), the [target axioms](../submissions/openai-20261028/checks/YangMills/OSRecon/Vendored/Axioms.lean) and the [growth condition](../submissions/openai-20261028/checks/YangMills/OSRecon/Growth.lean). The OPE check has its own [specification](../submissions/openai-20261028/checks/OPESpec.lean) and [proof](../submissions/openai-20261028/checks/OPECheck.lean).
4. Consult [the dated evidence](../submissions/openai-20261028/evidence/README.md) to see which targets and tools were checked, and [the reproduction instructions](../submissions/openai-20261028/docs/rerun.md) to rerun them. These distinguish Comparator runs from supplementary Lean compilations.

The assessment has the stable path [docs/assessment-1.pdf](assessment-1.pdf). Submission-specific explanations and examples live within [the October package](../submissions/openai-20261028/README.md).
