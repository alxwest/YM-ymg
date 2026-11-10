# Worked examples in Lean

These commented Lean files explain the October submission and the group’s checks beside statements that can be compiled and inspected in VS Code. They use the unchanged review specifications. Human readers still need to assess the interpretation in the comments; compilation checks the formal declarations and proofs.

The **A1–A8 labels follow the assessment’s evidence table**. A7 is combined acceptance; A8 is the separate OPE check.

| Assessment entry | Worked example | What it explains |
|---|---|---|
| A1 | [OSAxioms-20261028.lean](../../submissions/openai-20261028/docs/examples/OSAxioms-20261028.lean) | The selected stress-trace hierarchy, diagonal-flat Schwartz tests, E0–E4 and the arity-uniform E0′ estimate. |
| A2 | [OperatorContent-20261028.lean](../../submissions/openai-20261028/docs/examples/OperatorContent-20261028.lean) | Polynomial labels, correlation-null quotients, comparison with free on-shell field content, phase retention, cyclicity and faithfulness. |
| A3, A5 | [LatticeAndScale-20261028.lean](../../submissions/openai-20261028/docs/examples/LatticeAndScale-20261028.lean) | Plaquettes, coupling conversion and normalized Wilson laws; common RG calibration and the positive fixed-probe limit, distinguished from an intrinsic mass. |
| A4 | [LeadingTrace-20261028.lean](../../submissions/openai-20261028/docs/examples/LeadingTrace-20261028.lean) | The centered trace two-point function, its lattice origin through the mixed hierarchy, phase selection and the explicit leading short-distance coefficient. |
| A6 | [TranslationWard-20261028.lean](../../submissions/openai-20261028/docs/examples/TranslationWard-20261028.lean) | The tensor’s action on any inserted field: the ordinary coordinate derivative, fixed sign and coefficient, shell integrability and window independence. |
| A7; also A2, A3 | [OctoberChain.lean](../../submissions/openai-20261028/docs/examples/OctoberChain.lean) | Consequences of the construction data retained by combined acceptance: actual lattice insertions, full UV and extracted IR limits, phase algebra and reconstructed boundary distributions. |
| A8 | [CommonOPE-20261028.lean](../../submissions/openai-20261028/docs/examples/CommonOPE-20261028.lean) | Coefficient and finite-truncation remainder bounds, quantifier order, uniformity over phases, channel assembly and one-field recovery. |

All examples concern OpenAI’s 28 October 2026 submission. The [compilation and VS Code instructions](../../submissions/openai-20261028/docs/examples/README.md) explain how to read them in the review environment. The [initial compilation record](../../submissions/openai-20261028/evidence/examples-2026-11-10/result.json) covers OctoberChain and LeadingTrace; the [additional record](../../submissions/openai-20261028/evidence/examples-2026-11-10/additional/result.json) covers the other five.

These examples supplement the existing targets and historical Comparator evidence. They do not alter the acceptance requirements or constitute a new Comparator run.
