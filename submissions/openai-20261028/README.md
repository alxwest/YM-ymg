# OpenAI — 28 October 2026 submission and review

[All submissions and assessments](../../README.md)

## [Read the assessment (PDF)](../../docs/assessment-1.pdf)

The assessment, dated **10 November 2026**, explains the results, our verification checks, and the important questions left open. It is distributed as a PDF; its LaTeX source is maintained separately.

This package covers **OpenAI's submission of 28 October 2026**, the group's independent checks, and the evidence from building and checking it. It is part of the YM results repository.

The original submission is preserved byte for byte in [submission/](submission/). Our additions live outside that directory. The package includes the source needed for our checks, including bridges to previous relevant formalizations and their analytic dependencies; it does not require another private repository. Lean, Mathlib and Comparator are external tools or dependencies whose versions are pinned.

Start with [the checks and their scope](docs/checks.md), [the evidence record](evidence/README.md), and [how to rerun the checks](docs/rerun.md).

Seven [commented Lean examples](docs/examples/README.md) explain the assessment’s A1–A8 checks: lattice law and common scale, the lattice-to-continuum chain, operator content, scalar OS axioms, the translation Ward identity, the leading trace law, and OPE bounds. They contain compilable statements, explanations of the hypotheses and limits of each claim, and instructions for reading the code in VS Code.

The [documentation index](../../docs/README.md) gives a reading route through the specifications, proofs and evidence.

| Directory | Contents |
|---|---|
| `submission/` | Unmodified October source distribution, including its reference statement and solution |
| `checks/` | Combined acceptance specification and proof, OS bridges, lattice and other checks, and the separate OPE check |
| `verification/` | Comparator reference statements, configurations, tool pins and acceptance/rejection controls |
| `scripts/` | Portable reproduction runner using Python's standard library |
| `evidence/` | Dated build, warning, axiom and Comparator results, with their limitations |
| `provenance/` | Import hashes, upstream definition snapshots, licenses and correspondence records |
| `docs/` | Check descriptions, worked examples and reproduction instructions |

The main review theorem is `YMReview.Acceptance.combined_acceptance` in [CombinedAcceptance.lean](checks/CombinedAcceptance.lean). Its specification binds the lattice family, extracted limit and final witness together. The separate `YMReview.OPE.constructed` theorem in [OPECheck.lean](checks/OPECheck.lean) checks the source OPE against an explicit-radius formulation. See [the scope table](docs/checks.md) for what these statements establish and what they leave open.

For a fresh clone with Elan, Git, Python 3.10 or newer, and the usual Lean build prerequisites installed, run these commands from this package's root (`submissions/openai-20261028/`):

```sh
python3 scripts/verify.py integrity
python3 scripts/verify.py all
```

The second command builds the submission and review, builds the pinned tools, checks four Comparator controls, and runs Comparator on the submitted, combined and OPE endpoints. It uses the upstream **development launcher**, which works on macOS and does not provide Linux/Landrun isolation. Read [the rerun instructions](docs/rerun.md) before interpreting its result as a security audit. New results go into `runs/`; historical evidence is never overwritten.

## Making a submission

The shared [submission policy](../../README.md#making-a-submission) explains how to propose a new submission and the group's review discretion.

Code and documentation are licensed under [Apache-2.0](LICENSE), subject to the preserved upstream notices. See [NOTICE](NOTICE) and [submission/THIRD_PARTY.md](submission/THIRD_PARTY.md).
