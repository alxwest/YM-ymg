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

The 11 supplementary declaration audits in that run, original-package integrity checks,
six status-contract tests, conditional-proof rejection control, and the
19-declaration filtered-sector diagnostic all passed their scoped checks.
Neither the supplementary results nor the diagnostic establish the missing
native existence theorem or refute it.

The continued investigation adds `FiniteRegulatorTransport.lean`: three
proved translations of **actual finite-cutoff** Wilson asymptotics into
ym-lean's `RG.HasPerturbativeJet`. It also adds a checked scalar obstruction
to passing these jets through a merely pointwise regulator limit. These
results narrow the remaining work; they do not supply native acceptance.
The [continued-run evidence](evidence-2026-11-12-finite-regulator.json)
records all 14 supplementary declaration audits passing, all 10 scalar
diagnostic declarations passing, and the native existence submission
still rejected with exit 2 and its certificate false. Both original-source
integrity checks passed. The native inspector stopped at the incompatible
statement; it did not independently diagnose an analytic failure.

The [finite dictionary-change audit](audit/README.md) now transports a
complete **existing** native Ward family and scale normalization through a
smooth filtered correction. It constructs the new mixing and quantum-exact
primitive, proves the full computed residual identity and its UV-then-IR
limit, and proves equivalence of normalization existence for the two
presentations when the lower label has zero correction weight. The fresh
[226-declaration audit](audit/evidence/scale-normalization-transport-2026-11-12/result.json)
passes with only permitted axioms. It does not construct the starting
family or normalization from the October source, transfer the remaining
reconstruction data, or supply the missing all-orders continuum bridge.
The native existence candidate and admission status are unchanged.

The [output-recovery follow-up](audit/README.md) now transports the actual
native outgoing recovery relation at each fixed cutoff, retaining its
generated-Q primitive. Its [88-declaration audit](audit/evidence/output-recovery-2026-11-12/result.json)
also proves the exact condition for these inverse coefficient corrections
to agree across cutoffs. An independent two-label test shows that
invertibility of the dictionary alone does not guarantee this agreement.
This is not a generated Yang–Mills counterexample: the actual tails and
allowed exact remainders have not been evaluated on a same-flow family.
At that stage, incoming raw limits, global coefficient coherence and the
all-orders continuum matching remained open.

The [coherence continuation](audit/README.md) closes the outgoing
all-cutoff step for corrections between distinct labels of the same
positive engineering degree, with raw data fixed. It constructs one
distribution-valued output table and proves the native recovery, locality,
graph-order and collision-scaling fields. It also proves exactly when a
generated-Q remainder can repair a proposed coefficient change, and that
no such remainder exists at cutoffs `D ≤ 2`. The fresh
[131-declaration audit](audit/evidence/output-coherence-2026-11-12/result.json)
passes. That audit left the changed incoming extractor and raw limits
unproved. General downward corrections and the source's all-orders
continuum comparison remain unresolved.

The [incoming continuation](audit/README.md) now proves the finite
multilinear change on the actual native regulated extractor, its exact
coupling jets, all three native regularity fields, and the new local raw
distribution table's weak UV limits. It includes every incoming slot and
the anchored final insertion. Its [187-declaration audit](audit/evidence/incoming-raw-transport-2026-11-12/result.json)
checks 56 new declarations and rebuilds the previous 131. The incoming
transformation has a proved inverse when the lower label has zero weight.
These are conditional transport theorems: combining the new raw table
with outgoing physical recovery and coefficient bounds still needs a full
compatibility proof. They do not supply the October source's missing
all-orders continuum bridge. No native existence certificate is claimed;
the candidate and target are unchanged, and native admission was not rerun.

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

`FiniteRegulatorTransport.lean` uses the stronger source results
`YM.PertExtension.Orb.finite_formula` and `before_tree_formula`, not just
the formal series in `YM/Pert/Lattice/Series.lean`. Their remainder is
bounded by `C * g^(N+1)` at each fixed cutoff. The translation proves the
native `epsilon * g^N` bound for the same actual expectations and the same
finite-cutoff coefficients. It includes the source's Haar-expectation
version before tree reduction, with the source's even-side and observable
hypotheses preserved. Source mode checks these three declarations as well.

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
- The stronger `submission/YM/PertExtension/Normalized.lean` supplies
  actual finite-cutoff expansions. These have now been translated by
  `FiniteRegulatorTransport.lean`. The constants and small-coupling
  neighborhoods can depend on the cutoff. The supporting
  `OrbExpansion.lean`, `Interior.lean`, and `Uniform.lean` estimates retain
  that dependence; the name `Uniform` does not assert uniformity as the
  cutoff is removed.
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
acceptance. Source mode checks five limit-passage, six coordinate, and
three finite-regulator declarations against the permitted axioms. Fresh runs write full logs,
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

Tracking: `alxwest/ym-lean` issues #2 and #8, and the separate
[all-orders source review, #18](https://github.com/alxwest/ym-lean/issues/18).
The broader source-to-target
specification-equivalence question is not settled by this contribution.
Current physical/logic reviews are #24 and #26; the carrier-universe
translation is ym-lean PR #25.

## Continued attempt: the remaining analytic obstruction

The finite-cutoff translation closes an actual compatibility step, but
does not fill `RegulatedExpansion.uniform_remainder`. A direct proof of
the target's continuum matching could also close the gap; a
regulator-uniform estimate is sufficient for our route, not a mandated
proof method of the target.

The attempt to remove this hypothesis by a generic limit argument fails.
`audit/NonuniformLimit.lean` proves the following smooth scalar example
against the imported native `HasPerturbativeJet` definition:

```text
f(r, g) = 1 + g² exp(-r/g),  r > 0, g > 0
prescribed coefficients: a₀ = 1, aₖ = 0 for k > 0
```

For every fixed positive `r`, `f(r, ·)` has precisely that asymptotic jet
to every finite order. The coefficient sequence is constant in `r`, so
its coefficient limits exist. At every fixed positive `g`, taking `r`
to zero gives `1 + g²`. This continuum function still tends to 1 as `g`
goes to zero, so the leading term agrees, but its order-two error against
the prescribed jet is exactly `g²`; it cannot be at most `g²/2`.
The file also proves that the uniform order-two remainder bound fails.
All ten declarations are axiom-audited by:

```sh
python3 integrations/ym-lean/audit/check_nonuniform_limit.py \
  --ym-lean ../ym-lean --out integrations/ym-lean/runs/nonuniform-limit
```

This refutes the **generic promotion step**, not a Yang–Mills existence
claim, not the full source-to-target implication, and not the possibility
of establishing stronger estimates for the constructed theory.

Two additional source routes were checked:

- `YM.OPE.Measuring.simultaneous` supplies a common OPE and leading
  measuring data on the same `Final`. It avoids combining unrelated
  theories, but does not identify every coefficient in a coupling-power
  expansion with the native generated coefficients.
- `YM.PertExtension.Running.ratio` gives a leading running-coupling
  asymptotic. It does not supply the exact native beta-function jet,
  running-frame identities, or all-orders remainder estimates.

`FirstExtension.jets` and `Position.Crest` concern the mean hierarchy in
moving frames along the chosen scaling sequence. The target's
`AllOrderVacuumWordMatch` concerns the same actual physical vacuum words
at every sufficiently small real scale. Promoting between these statements
still needs proved phase/frame, coefficient, and scale identifications.
The investigation did not produce those estimates from the supplied
material. The branch therefore remains blocked on a mathematical
comparison theorem, in addition to the outstanding full candidate
assembly listed above.

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

## Requirement checks — 12 November 2026

The [follow-up audit](audit/README.md#results-of-the-12-november-follow-up)
checks label-permutation invariance, actual finite-cutoff Wick and curvature
kernels, the cutoff derivative, Gaussian subtraction, and the first possible
orders of the actual generated RG series. All 25 new Lean declarations pass
their axiom audits; independent Gaussian calculations agree with the scoped
kernel results. Five negative-control tests check the audit-log acceptance.

The decisive physical sector test remains unresolved: the renormalized
one-loop mixing coefficient and its associated same-prescription OPE channel
have not been identified. The audit explains why a bare Wick contraction
cannot replace that calculation. It proves neither necessity of every native
condition nor inconsistency of the target, and does not produce existence
acceptance.
