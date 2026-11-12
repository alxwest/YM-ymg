# Exact ym-lean existence admission — incomplete proof, draft integration

**This does not yet pass `ym-lean --claim existence`. No unconditional
existence theorem is supplied.** The supporting lemmas compile; that is
not the same as proof acceptance. The native status and certificate are
recorded separately from the helper checks. [evidence.json](evidence.json)
is the historical Lean 4.31.0 run; the current pin uses Lean 4.32.0.
The [12 November evidence](evidence-2026-11-12.json) records a fresh real
source submission on the new pin: compilation and the source audit passed,
but native admission exited 2 with `INCOMPATIBLE_PROOF_SIGNATURE` and
`existence_only_kernel_certificate=false`:

```text
Expected type: YangMills.YangMillsExistenceOnly.{u}
Submitted type: YMGBridge.PresentedJointExistence.{u}
Submitted universe parameters: [u]
```

The 11 supplementary declaration audits, original-package integrity checks,
six status-contract tests, conditional-proof rejection control, and the
19-declaration filtered-sector diagnostic all passed their scoped checks.
Neither the supplementary results nor the diagnostic establish the missing
native existence theorem or refute it.

## Submit the available October proof on Lean 4.32.0

With the pinned `ym-lean` checkout alongside this repository, run from the
repository root:

```sh
python3 integrations/ym-lean/verify_existence.py --ym-lean ../ym-lean --source
```

This checks original-package integrity, builds and audits the actual source
translation, checks the supplementary proofs, and submits
`YMGBridge.jointExistence` to the unchanged native existence verifier. The
source translation removes the old universe-count mismatch. It does not
turn `PresentedJointExistence` into `YangMillsExistenceOnly`; the native
verifier still needs an unconditional theorem of the latter type.

`SpacetimeTransport.lean` now gives a continuous linear coordinate
equivalence between the source's time-last Euclidean coordinates and the
target's time-first coordinates. It preserves the Minkowski square,
forward cone, and spacelike relation, and gives inverse continuous linear
maps on the actual Schwartz test spaces. This closes these coordinate
comparisons without changing either definition. It does not construct a
Wightman field system or a generated Yang–Mills sector.

All original source and historical evidence remain unchanged. The
`--source` result records source translation, coordinate transport, and
native acceptance separately; only native acceptance can return zero.

## What this change proves

`UniformPerturbativeLimit.lean` proves the missing *limit-passage operation*:
finite-regulator expansions with a regulator-independent small-scale
radius, convergent actual observations, and the prescribed coefficient
limits imply continuum all-order matching. The file supplies the exact
`YangMills.FilteredRG.AllOrderMultiMatch` and
`YangMills.FilteredRG.AllOrderVacuumWordMatch` predicates, conditional
on those estimates. It never replaces the coefficients or observation by
freely chosen approximations.

The filter is required to be nontrivial. A regulator-dependent radius
that collapses to zero is not sufficient. The bounds must hold at every
sufficiently small real scale, not only a selected sequence.

**Not proved here:** that the October constructed theory satisfies these
uniform estimates, that its coefficients equal the prescribed target
coefficients, or that all of `FilteredExistenceCandidate` can be built.

## Why the existing source results are not enough to instantiate it

At original source revision `55ba9fc36293b3f4d52c6b1f813169a0be76ee98`:

- `submission/YM/Pert/Lattice/Series.lean` supplies formal all-order
  coefficients at a **finite** regulator; it does not supply the uniform
  continuum remainder estimate.
- `submission/YM/Pert/FirstTarget.lean:FirstExtension.jets` supplies a
  **leading** free comparison along a weak scaling sequence. Its `j`
  quantifier is spatial derivative order, not perturbative loop order.
- `submission/YM/Pert/Position/Four.lean` explicitly distinguishes its
  leading comparison from all-order actual-versus-diagram matching.

The unchanged target additionally needs the exact group-dependent
Ward/Callan–Symanzik system, composites, full Wightman data, stress
identification, and every-order physical matching. These do not follow
from building the source or from matching one conventional beta coefficient.

## Exact acceptance command

Prepare a trusted checkout of `alxwest/ym-lean` at the revision in
[pin.json](pin.json), with its pinned Lean 4.32.0/Mathlib toolchain and cache.
From this integration directory:

```sh
python3 verify_existence.py --ym-lean /path/to/ym-lean \
  --proof-file /path/to/CompleteProof.lean --theorem CompleteProof.existence
```

The proof file must supply an unconditional theorem of the exact type
`YangMills.YangMillsExistenceOnly.{u}`, with one universe parameter, and
must be self-contained under the original verifier's import rules.
The support library is compiled into fresh temporary objects and is not
used to change the pinned verifier. An eventual proof may inline or
independently arrange imports of these supporting results. `--source`
arranges the existing staged source imports automatically; it cannot be
combined with an explicit proof file.

The runner refuses tracked changes to the pinned verifier, fingerprints
its trusted files, runs its **unchanged** `scripts/verify_submission.py
--claim existence`, and returns zero only for a native
`EXISTENCE_ONLY_KERNEL_PROOF_ACCEPTED` result with the actual certificate,
expected target, theorem name, and successful process exit.

Omitting `--proof-file` and `--theorem` intentionally reports
`PROOF_NOT_SUBMITTED` and exits 2. It does not create a placeholder proof.

The historical October Lean 4.32.0 source and all original manifests remain
unchanged. This directory now uses the same Lean 4.32.0 toolchain for the
source-to-target comparison.
There is no new mass-gap claim, no weakened target, and no new proof axiom.

## Rejection controls and reproducibility

```sh
python3 test_driver.py
python3 verify_existence.py --ym-lean /path/to/ym-lean
# Expected exit 2: no complete proof supplied.
python3 verify_existence.py --ym-lean /path/to/ym-lean \
  --proof-file tests/Conditional.lean --theorem YMYMGControl.conditional
# Expected exit 2 with INCOMPATIBLE_PROOF_SIGNATURE: the theorem is conditional.
```

The conditional file is a negative control, not a submitted candidate
construction. Six status-contract unit tests passing is not mathematical
acceptance. Source mode checks five limit-passage and six coordinate
declarations against the permitted axioms. Fresh runs write full logs,
input hashes, and the original native report under `runs/`.

## Remaining work before this can be a passing fix

1. Supply actual selected-phase regulator observations and coefficient
   limits in the target normalization, with uniform all-order remainders.
2. Identify the target's prescribed generated coefficients, RG frames,
   Ward/CS identities and stress observable with the same source theory.
3. Complete the all-group Wightman/field/kernel/Hamiltonian transport and
   assemble `FilteredExistenceCandidate G` for every allowed `G`.
4. Supply and run the exact unconditional theorem. Only native admission
   can change the recorded existence certificate to true.

Tracking: `alxwest/ym-lean` issues #2 and #8. The broader source-to-target
specification-equivalence question is not settled by this contribution.
Current physical/logic reviews are #24 and #26; the carrier-universe
translation is ym-lean PR #25.

## Filtered-sector diagnostic — 11 November 2026

[A separate checked audit](audit/README.md) identifies a finite-sector
projection/transport mismatch in the active filtered stripping formula: an
omitted higher output can contribute at order g² to a retained output even
when the frame entries agree on their overlap. Its 19 audited declarations
include an unconditional matrix counterexample, conditional evaluations of
the actual imported stripping formula, and a non-flat asymptotic tail.

This is not yet a generated-Yang--Mills countermodel or a proof that the
existence target is inconsistent. The fixed engine must still be shown to
realize the relevant channel. The native existence certificate remains
false; neither the target nor the verifier is patched.
