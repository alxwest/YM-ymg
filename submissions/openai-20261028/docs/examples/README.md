# Worked examples in Lean

These commented Lean files explain the October submission and the group’s checks beside statements that can be compiled and inspected in VS Code. They use the unchanged review specifications. Human readers still need to assess the interpretation in the comments; compilation checks the formal declarations and proofs.

Where a check uses a specific numerical coefficient or another result from the literature, the corresponding example gives the supporting references and explains the conventions used in the comparison. These citations support particular checks; they are not a general bibliography of the construction. The comments distinguish the literature calculation from the statement verified in Lean. For the trace two-point coefficient, see §5 of [LeadingTrace](LeadingTrace-20261028.lean).

The **A1–A8 labels follow the assessment’s evidence table**. A7 is combined acceptance; A8 is the separate OPE check.

| Assessment entry | Worked example | What it explains |
|---|---|---|
| A1 | [OSAxioms-20261028.lean](OSAxioms-20261028.lean) | The selected stress-trace hierarchy, diagonal-flat Schwartz tests, E0–E4 and the arity-uniform E0′ estimate. |
| A2 | [OperatorContent-20261028.lean](OperatorContent-20261028.lean) | Polynomial labels, correlation-null quotients, comparison with free on-shell field content, phase retention, cyclicity and faithfulness. |
| A3, A5 | [LatticeAndScale-20261028.lean](LatticeAndScale-20261028.lean) | Plaquettes, coupling conversion and normalized Wilson laws; common RG calibration and the positive fixed-probe limit, distinguished from an intrinsic mass. |
| A4 | [LeadingTrace-20261028.lean](LeadingTrace-20261028.lean) | The centered trace two-point function, its lattice origin through the mixed hierarchy, phase selection and the explicit leading short-distance coefficient. |
| A6 | [TranslationWard-20261028.lean](TranslationWard-20261028.lean) | The tensor’s action on any inserted field: the ordinary coordinate derivative, fixed sign and coefficient, shell integrability and window independence. |
| A7; also A2, A3 | [OctoberChain.lean](OctoberChain.lean) | Consequences of the construction data retained by combined acceptance: actual lattice insertions, full UV and extracted IR limits, phase algebra and reconstructed boundary distributions. |
| A8 | [CommonOPE-20261028.lean](CommonOPE-20261028.lean) | Coefficient and finite-truncation remainder bounds, quantifier order, uniformity over phases, channel assembly and one-field recovery. |

All seven concern the **28 October 2026 submission**.

A useful reading order is lattice and scale, OctoberChain, operator content, OS axioms, translation Ward identity, LeadingTrace, and OPE. OctoberChain explains connections retained by A7; it is a supplementary consequence audit, not a replacement for reading `AcceptanceSpec.lean` and `CombinedAcceptance.lean`. The OPE endpoint remains separate from the combined endpoint.

## Compile and inspect

Use the pinned Lean toolchain and dependencies described in [the reproduction guide](../rerun.md). From the October package root, with the submission already built, prepare a review project and copy the examples into it:

```sh
python3 scripts/verify.py prepare --run-dir runs/example-review
cp docs/examples/*.lean runs/example-review/project/
cd runs/example-review/project
lake build Review
lake env lean -o .lake/build/lib/lean/OctoberChain.olean OctoberChain.lean
for example in OSAxioms-20261028 OperatorContent-20261028 LatticeAndScale-20261028 TranslationWard-20261028 LeadingTrace-20261028 CommonOPE-20261028
 do
  lake env lean -o ".lake/build/lib/lean/$example.olean" "$example.lean" || break
 done
```

Compile OctoberChain first because LeadingTrace imports it. `lake build Review` supplies all 43 review modules, including the OPE dependencies. The run directory must be new; choose another name when repeating preparation. If the submission is not built, first run `python3 scripts/verify.py build` from the package root. This substantial dependency build is not needed each time an example is read.

Open the generated `runs/example-review/project/` directory in VS Code and read the copied Lean files there. The project provides the imports; hover over declarations and use Go to Definition to follow the underlying code. The maintained sources are the files in this examples directory. Copy intended edits back here and rerun the relevant compilation.

## Compilation records

The [initial record](../../evidence/examples-2026-11-10/result.json) covers OctoberChain and LeadingTrace. The [additional record](../../evidence/examples-2026-11-10/additional/result.json) covers the other five examples and compilation of their two OPE dependency modules. Both records are dated 10 November and include source hashes, command details, logs and printed axiom dependencies. The [LeadingTrace reference-update record](../../evidence/examples-2026-11-10/references/result.json) recompiles the current file after adding the literature calculation and citations; it also confirms that the formal code is unchanged.

These are ordinary Lean compilations using the existing October acceptance build. They are separate from the historical Comparator runs and do not constitute a fresh whole-submission rebuild. The examples add explanations and consequences of existing results, not new acceptance requirements.

For the checked targets and historical verification runs, see [the check scope](../checks.md) and [the evidence index](../../evidence/README.md).
