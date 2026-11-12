# Checks of extra ym-lean requirements

## Complete generated-data transport, 12 November

**The incoming/outgoing assembly is finished for distinct basis labels of
the same positive engineering degree. The requested native existence pass
is still blocked by the missing source-to-native construction and continuum
comparison.** These are conditional transport results about existing native
objects; they do not supply the objects from the October theorem.

[`GeneratedDataTransport.compatible_change`](GeneratedDataTransport.lean)
constructs the changed raw and physical coefficient tables together and
proves every field of the actual imported
`GeneratedEuclideanData.Compatible`. This includes the same-flow condition,
extractor regularity, raw locality and UV limits, physical locality and
graph order, every partial-collision scaling bound, and physical recovery
at every output cutoff. `compatible_exists_iff` proves equivalence of
existence of such compatible data in the two presentations.

The outgoing inverse correction is applied first; the finite incoming
expansion then acts on both its physical coefficients and the original raw
coefficients. [`IncomingRecoveryLinear.lean`](IncomingRecoveryLinear.lean)
transforms the native quantum-exact primitive with the same addition,
scalar multiplication and `(2,1)` order shift. It retains the actual Ward
map and the permitted primitive support. No Q-image is declared zero.
[`IncomingRecoveryCoherent.lean`](IncomingRecoveryCoherent.lean) reconciles
different enumerations of each active basis set, so one distribution-valued
table works at every cutoff. Neither argument assumes independence of the
quantum fields.

[`IncomingPhysicalBounds.lean`](IncomingPhysicalBounds.lean) proves the
incoming graph-order and collision bounds using only replacements with
nonzero weight. Equal engineering degree preserves the dimension of each
input slot, including the anchored last insertion. Together with the
outgoing bounds already proved, this supplies the full physical coefficient
bounds for the combined table.

[`GeneratedCoefficientFamilyTransport.lean`](GeneratedCoefficientFamilyTransport.lean)
then constructs the actual `LocalWardCoefficientFamily` of the changed
`LocalWardFlowFamily` at **every** subtraction scale. Its coefficient family
can be supplied together with the previously constructed
`GeneratedScaleNormalization`. For a smooth scale-dependent correction,
existence of these two witnesses together is equivalent in the two
presentations. The coefficient-family transport itself does not need scale
smoothness; the normalization transport does.

The [fresh combined audit](evidence/generated-data-transport-2026-11-12/result.json)
checks **400 declarations: 46 new and 354 from the preceding incoming,
outgoing, Ward-family and normalization audits**. All forty local modules
are rebuilt, warnings are errors, and only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Five audit-log controls pass. The
[manifest](evidence/generated-data-transport-2026-11-12/manifest.json)
records the tested revision, all 53 input hashes and compiled-module
hashes. The pinned ym-lean checkout is unchanged.

### The remaining source-to-native blocker

The old assembly gap is no longer the obstacle for this equal-degree
change. Applying the theorem to the October submission still requires a
starting native Ward/coefficient family and its link to the constructed
physical theory. In particular, the native sector separately requires
`RG.AllOrderMultiMatch` and `PhysicalWords.AllOrderVacuumWordMatch` for the
actual physical observations and prescribed generated series. The
transport above proves neither those matches nor physical reconstruction.

I rechecked the finite-regulator routes rather than assuming their names
supplied the needed estimate. The original
[`OrbExpansion.laplace`](../../../submissions/openai-20261028/submission/YM/PertExtension/OrbExpansion.lean),
[`Normalized.finite_formula`](../../../submissions/openai-20261028/submission/YM/PertExtension/Normalized.lean),
[`LatticePT.finite`](../../../submissions/openai-20261028/submission/YM/PertExtension/FiltrationRule.lean)
and [`Mixed.comparison`](../../../submissions/openai-20261028/submission/YM/PertExtension/MixedRule.lean)
give expansions at each fixed lattice regulator. Their constants and
small-coupling thresholds are not supplied uniformly as that regulator is
removed. The fixed finite-dimensional Taylor estimates in
[`Uniform.lean`](../../../submissions/openai-20261028/submission/YM/PertExtension/Uniform.lean)
do not remove that dependence.

The continuum
[`FirstExtension.jets`](../../../submissions/openai-20261028/submission/YM/Pert/FirstTarget.lean)
controls spatial derivatives of a leading comparison along a scaling
sequence; its derivative order is not a coupling-loop expansion order.
The group's separate
[`AFSourceBridge`](../../../submissions/openai-20261028/checks/AFSourceBridge.lean)
also gives the stronger full punctured-space *leading trace* comparison.
That still does not supply arbitrary higher coupling orders. The group's
[check scope](../../../submissions/openai-20261028/docs/checks.md) explicitly
distinguishes this leading result from all-orders matching.

One sufficient way past the limit-passage obstacle is the already proved
[`all_orders_of_uniform_regulated_estimates`](../UniformPerturbativeLimit.lean):
for each finite order and error tolerance, a small-scale radius must work
before taking the regulator limit, with the prescribed coefficient limits.
A direct proof of the continuum matches could also suffice. I have not
derived either from the available construction. The checked scalar example
in [`NonuniformLimit.lean`](NonuniformLimit.lean) shows why fixed-regulator
jets, coefficient limits and a leading continuum limit alone cannot replace
that step. It is not a Yang--Mills counterexample or a proof that the
October theory cannot satisfy the native requirement.

Consequently the source existence candidate and its incompatible native
signature are unchanged. Native admission was not rerun, and
`existence_only_kernel_certificate` remains false. No passing existence PR
is claimed. Strict degree-lowering changes also remain outside the full
transport theorem proved here.

To reproduce the combined scope:

```sh
python3 integrations/ym-lean/audit/check_generated_data_transport.py \
  --ym-lean /path/to/ym-lean \
  --out /path/to/a/fresh/generated-data-audit
```

## Native incoming extraction and raw limits, 12 November

**The incoming raw-limit step is now proved, conditional on existing native
regularity and raw limits.** The proof starts with ym-lean's actual finite
insertion expansion, differentiates its coupling dependence, integrates
against its permitted relative tests, and takes the UV limit. It constructs
one local distribution-valued raw table, rather than selecting numbers
separately for each test. This works for a filtered direction whose lower
label is represented in the basis; equal engineering degrees are not needed
for this incoming result.

For the dictionary change `O'_p = O_p + hbar g^2 a chi(p) O_q`, every
incoming slot contributes either its original label or its `q` correction.
The finite expansion includes the final insertion anchored at zero. Its
coupling jets therefore have the exact form

```text
R' = (product over incoming slots of (1 + a chi(p) delta replace_by_q)) R,
delta R(order+2, loop+1) = R(order, loop), zero at the boundary.
```

The product is a finite multilinear operation on input labels, not an
infinite perturbative sum. `IncomingFiniteTransport.lean` and
`IncomingNativeExtractor.lean` identify it with the native
`liftedInsertionExpansion`, `liftedRegulatedCoefficient` and
`liftedCouplingCoefficient`. `IncomingTaylorTransport.lean` proves the
derivative identity, including the factorial normalization and boundary
orders. `IncomingNativeLimits.lean` transports all three fields of the
native `LiftedCoefficientRegularity`: coupling smoothness, graph grading
and test integrability.

[`GeneratedIncomingRaw.lean`](GeneratedIncomingRaw.lean) constructs
`incomingRaw` and proves the literal native `raw_limit` condition for the
changed lift, as well as locality of every new raw distribution. The test
identity is applied on the test's support, where its noncollision guards
hold; outside the support both integrands vanish. Only finite sums and
scalar multiples are moved through integration and the UV limit.
[`IncomingExpansionInverse.lean`](IncomingExpansionInverse.lean) also proves
that the whole incoming expansion is inverted by negating the weight when
`chi(q)=0`, and that native regularity is equivalent in the two presentations.

The [fresh audit](evidence/incoming-raw-transport-2026-11-12/result.json)
checks **187 declarations: 56 new and 131 from the preceding audit**. All
twenty local modules are rebuilt in an empty output directory with warnings
as errors, only the three permitted axioms, and five audit-log controls.
The [manifest](evidence/incoming-raw-transport-2026-11-12/manifest.json)
records source and compiled-module hashes. The pinned native target is unchanged.

That audit did **not** yet join the new raw table with the preceding outgoing
table in a full `GeneratedEuclideanData.Compatible` proof: simultaneous
incoming/outgoing physical recovery and the associated physical coefficient
bounds remained to be assembled; the combined audit above now supplies them
for the stated equal-degree change. It also does not construct the starting
native family from the October submission, prove its missing all-orders
continuum comparison, or transport physical reconstruction. Finite weak
limits of individual coefficients do not establish that all-orders
comparison. The native existence candidate is unchanged and was not rerun;
`existence_only_kernel_certificate` remains false.

To reproduce this scope:

```sh
python3 integrations/ym-lean/audit/check_incoming_raw_transport.py \
  --ym-lean /path/to/ym-lean \
  --out /path/to/a/fresh/incoming-raw-audit
```

## Exact remainders and coherent outgoing transport, 12 November

**The outgoing cutoff-coherence step is now solved for elementary changes
between distinct basis labels of the same positive engineering degree,
with the raw data held fixed.** A single distribution-valued coefficient
table satisfies the actual native recovery field at every cutoff, as well
as its locality, graph-order and partial-collision scaling bounds.

For general coefficient changes, the permitted quantum-exact remainder is
now handled by a necessary-and-sufficient native criterion. At cutoffs
`D ≤ 2` that remainder is proved to vanish because there are no allowed
primitives. These results do not construct an original interacting family,
transport the changed incoming extractor, or prove all-orders continuum
matching. Native existence admission remains incomplete.

The [131-declaration audit](evidence/output-coherence-2026-11-12/result.json)
checks **43 new declarations and 88 dependencies**, rebuilding all twelve
local modules. The [logs](evidence/output-coherence-2026-11-12/) and
[manifest](evidence/output-coherence-2026-11-12/manifest.json) record source
and compiled-module hashes. Warnings are errors, only `propext`,
`Classical.choice` and `Quot.sound` are permitted, and five audit-log controls
pass. The pinned ym-lean target is unchanged.

### Exactly when a remainder repairs recovery

[`OutputRecoveryExact.lean`](OutputRecoveryExact.lean) keeps the native
`quantumExactOutputVector`, its finite primitive support, the same `W` and
`Q`, and the compact nonexceptional external tests. Given an old recovery
and a proposed coefficient table obeying the required graph bound,
`recovery_iff_exact` proves:

```text
the proposed table has native recovery
  iff
its outgoing distribution minus the old outgoing distribution
  is Q(h) for one allowed primitive h, on every allowed test.
```

If the old primitive is `p`, the constructed new primitive is `p-h`.
Conversely, any new recovery supplies such an `h` by subtracting its
primitive from `p`. The support and linearity arguments are checked
against the actual imported expressions. This is an exact criterion for
recovery, not an assertion that a required primitive has been found for
the October theory.

`corrected_recovery_iff_exact` applies the criterion after the preceding
finite dictionary correction. `recovery_of_equal_outputs` also proves
that numerical coefficient tables need not be identical when their
outgoing distributions agree on the allowed tests. Thus the earlier
weighted-tail condition is necessary for equality of that explicit
coefficient construction, but need not be necessary for physical recovery.

`no_recovery_of_separating_test` gives a converse test: one allowed test
that annihilates the image of **every** supported primitive and detects the
output difference rules out recovery. No arbitrary Q-image is silently
declared zero.

### Where the remainder definitely cannot help

[`OutputRecoveryLowCutoff.lean`](OutputRecoveryLowCutoff.lean) proves that
every engineering-dimension-zero native monomial is the constant monomial.
Its ghost number is zero. For `D ≤ 2`, a permitted primitive would need
both `dimension + 1 < D` and ghost number `-1`, which is impossible.
Consequently:

```text
outputPrimitiveMonomials G D = empty,              D ≤ 2
rawOutputDistribution W D (quantumExactOutputVector Q D p) = 0.
```

The second statement holds for arbitrary `Q` and `p`: it does not replace
the actual Ward map by zero or require a physical quotient theorem.
`recovery_low_iff` reduces recovery at these cutoffs to equality of the
actual outgoing distributions. `no_low_recovery` rules out repairing a
nonzero difference detected by one permitted test. Neither theorem assumes
injectivity of the quantum field correspondence.

The bound is checked against a positive control. At cutoff three, the
native single antighost monomial has degree one, ghost number `-1` and odd
parity, and is an allowed primitive. Its color index is explicit. The
empty-primitive argument therefore cannot be extended to that cutoff.
Existence of a primitive does not establish that its Q-image can absorb a
particular discrepancy.

### A common table that works at every cutoff

[`OutputRecoveryCoherent.lean`](OutputRecoveryCoherent.lean) constructs the
coordinate direction for two distinct positive-degree basis labels and
the global inverse coefficient correction

```text
J'_high = J_high + a delta J_low
C'_i = C_i - [i=low] a delta C_high.
```

Here `delta` is the zero-extended `(2,1)` coupling/loop shift. The native
unit condition and intrinsic filtration of the direction are proved.
When the two labels have the same engineering degree, every active set
contains either both labels or neither. The finite-cutoff recovery proofs
therefore use restrictions of this **one** table. The coefficient inverse
and dictionary inverse establish
`coherent_recovery_same_degree_iff` for the complete outgoing all-cutoff
relation, with the raw vector fixed.

For a strictly downward correction, `sector_recovery` and
`outside_window_joint` show that the same construction works outside

```text
dimension(low) < D ≤ dimension(high).
```

Only that finite interval separates the selected coordinate labels. The
exact-image criterion above identifies what would repair the discrepancy
inside the interval; no such same-flow repair is claimed here.

[`GeneratedOutputTransport.lean`](GeneratedOutputTransport.lean) constructs
`changeOutputs E high low a` as one `GeneratedEuclideanData` record. Its
physical entries are actual linear distributions, defined independently
of the test later applied. The following native fields are proved for the
changed outgoing table, given an original compatible `E`:

- `outputs_recovery`: the literal `physical_recovery` quantifier, using
  the changed dictionary and the same corrected table for every cutoff.
- `outputs_graph`: the required lower bound on coupling order at each loop.
- `outputs_local`: finite-order local distribution continuity.
- `outputs_scaling`: the original partial-collision power-counting bounds.

Equal output degrees justify the last field. The finite linear combination
preserves the bounds for every collision cluster; no ultraviolet or
infrared limit is interchanged. The original raw data are retained.

### Remaining bridge

`changeOutputs` is **not** accompanied by a proof of the full native
`GeneratedEuclideanData.Compatible` structure. Changing the dictionary
also changes the incoming products used to generate `raw`. Their extractor
regularity and actual weak raw limits still need transport. Keeping the
old raw data is justified here only for the isolated outgoing step.
General strictly downward changes also retain the finite-interval
exact-image obligation described above.

No nonzero obstruction has been computed for the actual October same-flow
theory; no inconsistency of either existence target follows. The earlier
normalization equivalence remains valid, and the all-orders continuum
comparison in [ym-lean #27](https://github.com/alxwest/ym-lean/issues/27)
remains unproved. The submitted existence theorem is unchanged, so no
new native admission run or rejection is claimed.

Reproduce from the YM-ymg checkout with a fresh directory:

```sh
python3 integrations/ym-lean/audit/check_output_coherence.py \
  --ym-lean ../ym-lean \
  --out integrations/ym-lean/runs/output-coherence-new
```

The scoped status is `SCOPED_OUTPUT_COHERENCE_CHECKED`. Exact-image,
low-cutoff and equal-degree outgoing-field flags are true. Full generated
compatibility, incoming raw-limit transport, general downward recovery,
a concrete same-flow obstruction and existence acceptance remain false.

## Output recovery at fixed and varying cutoffs, 12 November

**The dictionary correction now transports the actual native outgoing
recovery relation at a fixed cutoff.** Existence of recovery is equivalent
before and after the correction, with its hypotheses retained. Transport
of one global generated coefficient family is still unproved: the explicit
inverse corrections at different cutoffs need not agree.

The [88-declaration audit](evidence/output-recovery-2026-11-12/result.json)
checks **29 new declarations and 59 dependencies**, rebuilding eight local
modules against the unchanged pinned target. The
[logs](evidence/output-recovery-2026-11-12/) and
[manifest](evidence/output-recovery-2026-11-12/manifest.json) record source
and compiled-module hashes. Warnings are errors; only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Five audit-log controls
pass. This is a scoped helper audit, not native existence admission.

### What is transported

At a fixed scale, write the corrected dictionary as

```text
J'_i = J_i + a w_i delta J_k,       w_k = 0,
```

where `delta` shifts coupling/loop order by `(2,1)` with zero extension.
For a finite active set `S` containing the lower label `k`, define

```text
T_S = sum_{j in S} w_j C_j
C'_{S,i} = C_i - [i=k] a delta T_S.
```

[`OutputCoefficientShear.lean`](OutputCoefficientShear.lean) proves exact
cancellation through the double Cauchy convolution and preservation of
the coefficient graph bound `order < 2*loop → C = 0`.
[`OutputRecoveryTransport.lean`](OutputRecoveryTransport.lean) identifies
this assembly with the imported `liftedOutputDistribution` and proves
`recovery_corrected` for the **complete** `QuantumPhysicalOutputRecovery`
predicate. Its generated-Q primitive is unchanged; the compatibility,
insertion limits, Ward identities and primitive support are retained.

If the correction vanishes on the active labels, `recovery_fixed` retains
the old coefficients. `inactive_weights` derives this case when the cutoff
is no greater than the lower label's degree. `recovery_exists_iff` uses
the inverse correction `-a` to prove equivalence of recovery existence
when the lower label is active or all active weights vanish.

The raw vector is held fixed in these theorems. Changing the dictionary
also changes **incoming** regulated products in the full generated-data
structure. Their new raw limits and power-counting bounds have not been
transported here. Thus these results discharge the outgoing recovery step
conditionally, not all of `GeneratedEuclideanData.Compatible`.

### The additional condition across cutoffs

The native [`GeneratedEuclideanData.Compatible.physical_recovery`](https://github.com/alxwest/ym-lean/blob/baecbb5eba5710fb707cfaecfaf7365d8feff5f7/YangMills/GeneratedEuclideanCoefficients.lean#L111-L118)
uses restrictions of the **same** `E.physical` for every engineering cutoff
`D`. Meanwhile [`rawOutputDistribution`](https://github.com/alxwest/ym-lean/blob/baecbb5eba5710fb707cfaecfaf7365d8feff5f7/YangMills/QuantumOutputRecovery.lean#L29-L36)
truncates the raw monomial outputs using `monomialsBelow G D`. That
projection is specified independently of the corrected dictionary.

[`OutputRecoveryCutoffs.lean`](OutputRecoveryCutoffs.lean) proves that the
finite-enumeration correction above is exactly the active-set formula,
independently of enumeration order. For `S ⊆ T`, the two corrections differ
at the common lower label by

```text
C'_{T,k}(r+2,l+1) - C'_{S,k}(r+2,l+1)
  = -a sum_{j in T\S} w_j C_j(r,l).
```

`correction_coherent_iff` proves that these corrected coefficients agree
on the overlap **if and only if** this weighted omitted tail, multiplied
by `a`, vanishes at every coupling and loop order. This criterion concerns
the explicit inverse correction. It does not prove uniqueness of quantum
physical coefficients or exclude another choice differing by allowed
exact terms.

Two further theorems use the actual native definitions.
`raw_cutoff_difference` is the exact sum over the added raw monomials.
`recovery_cutoff_difference` proves that two native recovery witnesses obey

```text
raw_T - raw_S = (lifted_T - lifted_S) + (Q-remainder_T - Q-remainder_S).
```

Both generated-Q remainders, their genuine primitive witnesses and their
cutoff-specific supports remain explicit. No physical Ward quotient is
assumed, and no exact remainder is silently set to zero.

### A decisive finite test, with a limited scope

The two-label test takes independent coordinates `L,H` and changes
`H` to `H + a delta L`, leaving `L` fixed. The raw vector has low part
`R_L` and high part `R_H`. A shared pair of coefficients `A,B` must solve

```text
small cutoff:  A = R_L
large cutoff:  A + a delta B = R_L,     B = R_H.
```

`simultaneous_iff` proves that a solution exists exactly when
`a R_H(r,l)=0` for every `r,l`. With `a=1`, `R_L=0` and the constant unit
jet `R_H=1`, no shared pair exists: the first discrepancy is at `(2,1)`.
The two assembly lemmas check these coordinate equations using the same
finite Cauchy-convolution operation as native output recovery.

Positive controls prove recovery before the change (`a=0`) and full-space
recovery afterwards with `A=R_L-a delta R_H`, `B=R_H`. The constant high
jet respects the coefficient graph-order bound. Thus the obstruction is
simultaneous agreement with the smaller raw projection, not failure to
invert the dictionary or an impermissible loop degree.

**This is a finite algebraic model with independent directions and no exact
remainder. It is not a generated Yang–Mills model, does not establish
inconsistency of ym-lean, and does not show that the October theory has a
nonzero obstructing channel.** The native basis has classical independence;
quantum independence and detection of exact terms do not follow from that.

### What is still needed

To extend the completed normalization transport to the full generated
coefficient family, one must handle the incoming raw limits and establish
coherence of outgoing recovery. The explicit correction works globally
if its weighted tails vanish. More generally, the native recovery equation
allows a different coefficient choice if the discrepancy can be absorbed
by its permitted generated-Q primitives. Neither property has been proved
for a concrete same-flow family supplied by the October construction.

Conversely, demonstrating a real obstruction would require an actual
nonzero generated tail and a permitted test or proved quotient on which
the relevant exact remainders vanish. The finite test alone supplies
neither. Changing the target's raw projection or dropping coherence is
therefore not justified by this audit.

The earlier normalization-existence equivalence remains valid within its
stated scope. The source's missing all-orders continuum matching also
remains unresolved, as tracked in [ym-lean #27](https://github.com/alxwest/ym-lean/issues/27).
The earlier filtered-sector diagnostic below concerns a related projection
issue in RG stripping; this result checks the separate outgoing recovery
clause before RG matching. The native existence candidate is unchanged,
so admission was not rerun and no new verifier rejection is claimed.

Reproduce from the YM-ymg checkout with a fresh output directory:

```sh
python3 integrations/ym-lean/audit/check_output_recovery.py \
  --ym-lean ../ym-lean \
  --out integrations/ym-lean/runs/output-recovery-new
```

The success status is `SCOPED_OUTPUT_RECOVERY_CHECKED`. The flags for full
generated-family transport, a same-flow nonzero tail, a generated
countermodel, native-target inconsistency and existence acceptance remain
false. The sections below retain the scopes of their earlier audits.

## Complete scale-normalization transport, 12 November

The quantum-exact primitive gap is now closed. **Given an existing native
`GeneratedScaleNormalization`, the corrected dictionary has a complete
native `GeneratedScaleNormalization`**, with constructed mixing and
primitive data and the full computed composite residual equation.

There is also a proved equivalence of normalization existence for the two
presentations, under the explicit hypotheses that the correction is smooth
on positive scales and `χ(q)=0`:

```text
Nonempty (GeneratedScaleNormalization (changeFamily family D a))
  ↔ Nonempty (GeneratedScaleNormalization family).
```

This is **not** an existence proof for either presentation. The original
family and its normalization are not constructed from the October YM-ymg
source. The theorem does not compare the complete ym-lean and YM-ymg
existence statements or establish necessity of every extra native field.

The [226-declaration audit](evidence/scale-normalization-transport-2026-11-12/result.json)
checks **25 new declarations and 201 dependencies**, rebuilding all 20 local
modules against the unchanged pinned target. The
[logs](evidence/scale-normalization-transport-2026-11-12/) and
[manifest](evidence/scale-normalization-transport-2026-11-12/manifest.json)
record source and compiled-module hashes. Warnings are errors; the only
permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.
Five audit-log control tests pass.

### Smoothness from the actual finite construction

[`ExactInsertionSmoothness.lean`](ExactInsertionSmoothness.lean) proves the
coupling smoothness needed before taking Taylor coefficients of the
quantum-exact insertion. It uses the actual generated Ward coefficient,
including the classical master-action differential and the same transported
anomaly, rather than a separately supplied smooth Ward operator.

For the classical part, `actionLinear` proves that the local differential is
linear in its action argument. Applying a scalar monomial extractor to the
native finite master-action vertex list then gives a smooth coupling
polynomial. The anomaly's native graph grading supplies its smoothness.

The primitive's graph power similarly supplies coupling smoothness and
proves that its support at any coupling is contained in its support at
coupling one. `exactInsertion_fixed_support` rewrites the native expression
using those fixed finite sets. This justifies differentiating the finite
sums without assuming uniform support separately. Coupling smoothness of
the insertion flow comes from the existing fixed flow equations.

### The primitive and its computed transform

[`PrimitiveTransport.lean`](PrimitiveTransport.lean) constructs

```text
P'_p(mu,g) = P_p(mu,g) + hbar g² a(mu) χ(p) P_q(mu,g).
```

`changePrimitive` fills every native `LocalScalePrimitive` field: intrinsic
support, admissibility, ghost number, parity, joint scale/coupling smoothness,
classical vanishing and graph power. The support argument uses the same
filtered direction as the dictionary change; no larger degree bound is
chosen. The generated-Q insertion identity is proved by reindexing its exact
finite loop sums, with the original Ward operator and insertion flow.

[`ExactLegendreTransport.lean`](ExactLegendreTransport.lean) passes that
identity through the actual coupling jets and deterministic Legendre
recursion. Writing `E_p` for the computed `quantumExactGamma`, it proves

```text
E'_p = E_p + a(mu) χ(p) delta E_q,
```

where `delta` is the zero-extended `(2,1)` coupling/loop shift. The smoothness
proved above justifies the Taylor product rule at every finite order.

### Full residual and normalization

[`ScaleNormalizationTransport.lean`](ScaleNormalizationTransport.lean)
combines the primitive identity with the preceding mixing calculation.
For the **complete native residual**, it proves

```text
R'_p = R_p + a(mu) χ(p) delta R_q.
```

The identity holds at `0 < mu < UV`. That is enough for the native
UV-then-IR weak endpoint condition: at each positive IR, the identity holds
eventually as UV grows, and the old residuals already have zero endpoint
limits. The compact-test and nonexceptional-support restrictions are
unchanged. No interchange of limits is introduced.

`changeNormalization` fills every field of the actual
`GeneratedScaleNormalization (changeFamily family D a)`. The beta, field
coefficients, background and action primitive are the original ones; the
constructed mixing and composite primitives account for the dictionary
change. `normalization_exists_iff` proves the reverse implication using
the correction with coefficient `-a` and the earlier exact family inverse.
It asserts equivalence of existence, not equality of the freely represented
mixing tables after round-trip transport.

This completes the finite dictionary-change test through the full native
Ward-family and scale-normalization structures. Generated coefficient
recovery, physical reconstruction and the source's all-orders continuum
matching remain outside this result. The broader bridge blocker remains
[ym-lean #27](https://github.com/alxwest/ym-lean/issues/27). The existence
candidate is unchanged, and no new native admission run was made.

Reproduce from the YM-ymg checkout with a fresh output directory:

```sh
python3 integrations/ym-lean/audit/check_scale_normalization_transport.py \
  --ym-lean ../ym-lean \
  --out integrations/ym-lean/runs/scale-normalization-transport-new
```

The scoped status is `SCOPED_SCALE_NORMALIZATION_TRANSPORT_CHECKED`.
Primitive, full residual, scale-normalization transport and normalization
existence-equivalence flags are true. Original family/normalization
construction, full existence acceptance and necessity of the complete
native target remain false. The sections below retain the scopes and open
obligations of their earlier audits.

## Native mixing construction and cancellation, 12 November

The changed **native `CompositeMixing` is now constructed**, including every
filtration, smoothness, classical, unit and input-linearity field. Its graph
order is preserved. The actual native differential-plus-mixing expression
transforms covariantly, with both derivative corrections cancelling at every
finite coupling and loop order for `0 < mu < UV`.

This resolves the mixing construction left open in the preceding scale
audit below. It still assumes an existing `LocalWardFlowFamily` and
`GeneratedScaleNormalization`. Transport of the quantum-exact primitive and
the complete residual remain open; no complete changed normalization or
existence certificate is claimed.

The [201-declaration audit](evidence/mixing-transport-2026-11-12/result.json)
checks **70 new declarations and 131 dependencies**, rebuilding all 16 local
modules. The [logs](evidence/mixing-transport-2026-11-12/) and
[manifest](evidence/mixing-transport-2026-11-12/manifest.json) record source
and compiled-module hashes. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted; warnings are errors and five audit-log control tests pass.

### Avoiding an extra support assumption

[`FilteredLabelShear.lean`](FilteredLabelShear.lean) constructs the fixed
linear equivalence

```text
T(p) = p + χ(p)q,       T^-1(p) = p - χ(p)q,
```

under the explicit condition `χ(q)=0`. Both directions preserve the intrinsic
filtration; in fact `dim(T(p)) = dim(p)`. Pushing a finite output coefficient
table along this fixed equivalence and subtracting the old table defines
`L = push_T - id`. Each coordinate is exactly

```text
(L c)(r) = c(T^-1(r)) - c(r).
```

Thus its smoothness follows from two **fixed** old coordinates. There is no
derivative of a sum with moving support. For any real-linear observable
dictionary `J`, the finite evaluation of `L c` is proved to equal
`(sum_r c(r) χ(r)) J(q)`. This is an identity of evaluations, not a claim
that `L²=0` as a map on the free coefficient tables.

### The complete coefficient formula

[`MixingCoefficientTransport.lean`](MixingCoefficientTransport.lean) builds
all the native mixing operations used in the change. Let `delta` mean the
zero-extended `(2,1)` delay and let `eta` mean the `(1,1)` delay. At a fixed
scale, the constructed output table for input `p` is

```text
K'_p = K_p + a χ(p) delta K_q
       - a delta(L K_p) - a² χ(p) delta²(L K_q)
       - χ(p) [mu a' pulse_(2,1) + 2a eta(beta)] [q].
```

Here `[q]` is the singleton output table and `pulse_(2,1)` is one only at
coupling order two and loop order one. The coefficient function `a` is
assumed smooth on positive scales. The derivative is the actual real
derivative of that function. The quadratic cross term is retained even
when the direction preserves rather than strictly lowers dimension.

`changeMixing_graph` proves the native `order < 2*loop` guard from the old
mixing guard and `beta(order,loop)=0` for `order < 2*loop+1`. No independent
new beta, field coefficients or flow are introduced.

### Checked against the native action

[`MixingActionTransport.lean`](MixingActionTransport.lean) and
[`MixingRateTransport.lean`](MixingRateTransport.lean) prove the formula's
action using the target's exact finite sums and the column-label convention.
For `J'_p = J_p + a χ(p) delta J_q`, they establish

```text
mix(K', J')_p = mix(K, J)_p + a χ(p) delta mix(K, J)_q
                - mu a' χ(p) delta J_q
                - 2a χ(p) betaAction(eta J_q).
```

[`NativeMixingTransport.lean`](NativeMixingTransport.lean) proves that the
**actual computed** `liftedGamma` is a real-linear dictionary, using the
original finite lift's linearity, its coupling smoothness and the proved
Legendre recursion. It then applies the formula to the actual changed
family. `family_differential_mixing_change` combines it with the previous
native derivative theorem and proves

```text
(differentialPart J' + mix(K', J'))_p
  = (differentialPart J + mix(K, J))_p
    + a χ(p) delta(differentialPart J + mix(K, J))_q.
```

The signs, factor of two, scale derivative and quadratic mixing term are
therefore checked by Lean against the native definitions. This is still
the expression **before subtracting the quantum-exact insertion**. A new
`LocalScalePrimitive` and its actual `quantumExactGamma` transport must be
proved before the weak-limit closure lemmas yield the complete equation.

The earlier nonzero beta-term control shows why keeping the old mixing is
insufficient in general. The new construction shows how that term is
absorbed consistently. It does not establish that every extra requirement
in ym-lean is necessary, nor supply missing all-orders continuum matching
from the October YM-ymg source. The broader blocker remains
[ym-lean #27](https://github.com/alxwest/ym-lean/issues/27).

Reproduce from the YM-ymg checkout with a fresh output directory:

```sh
python3 integrations/ym-lean/audit/check_mixing_transport.py \
  --ym-lean ../ym-lean \
  --out integrations/ym-lean/runs/mixing-transport-new
```

The scoped success status is `SCOPED_MIXING_TRANSPORT_CHECKED`. The changed
mixing and native differential-plus-mixing flags are true; complete
residual, scale-normalization and existence-certificate flags remain false.

## Computed Legendre and scale-derivative transport, 12 November

The correction now passes through the **actual recursive Legendre insertion**,
and the changed family satisfies the native joint scale/position/momentum
smoothness field when the correction coefficient is smooth. Its complete
scale/coupling/field differential term has also been transported, retaining
both product-rule contributions. This closes the Legendre-formula and
`CompositeCSConditions.lifted_scale_smooth` gaps left by the previous audit.

It does **not** yet construct the changed mixing or quantum-exact primitive,
prove cancellation of the full composite residual, or supply a complete
`GeneratedScaleNormalization`. The original interacting family and its
normalization remain hypotheses, and the existence candidate is unchanged.

The [131-declaration run](evidence/scale-derivative-transport-2026-11-12/result.json)
checks **51 new declarations and 80 dependencies**, rebuilding all local
modules afresh against the unchanged pinned target. The
[logs](evidence/scale-derivative-transport-2026-11-12/) and
[manifest](evidence/scale-derivative-transport-2026-11-12/manifest.json)
record the exact source and compiled-module hashes. Warnings are errors;
only `propext`, `Classical.choice` and `Quot.sound` are allowed as transitive
axioms. Five audit-log control tests also pass.

### The computed transform, at every finite order

[`TupleJetShift.lean`](TupleJetShift.lean) reindexes the native finite
coupling/loop allocations. It identifies the bounded `Fin` assignments
with tuples having the prescribed total, and shifts only the outer vertex's
orders. The root orders, partitions, signs and covariance are unchanged.
Boundary cases with insufficient coupling or loop order vanish explicitly.

[`LegendreDictionaryTransport.lean`](LegendreDictionaryTransport.lean)
uses that reindexing to prove, for the actual native definitions:

- `meanFieldCompose_delay`: the complete finite mean-field composition
  commutes with the `(2,1)` coupling/loop delay.
- `insertion_add`, `insertion_smul`, `insertion_delay`: the deterministic
  `insertionGammaCoeff` recursion is linear and commutes with that delay.
  These identities do not require a separately assumed inverse equation.
- `flowJet_change` and `liftedGamma_change`: actual finite insertion jets
  and their computed Legendre transforms obey the dictionary correction.
  Coupling smoothness comes from the original insertion-limit compatibility.
- `family_liftedGamma_change`: the same identity for the exact positive-scale
  extensions used by the native family and scale-normalization structures.
- `changeFamily_scale_smooth`: the precise joint smoothness field, using
  an existing normalization and explicit smoothness of `a(mu)` on positive
  scales. There is no inference of scale smoothness from pointwise data alone.

Writing `J_p` for the computed insertion, and `delta` for the zero-extended
shift `(r,l) -> (r-2,l-1)`, the proved formula is

```text
J'_p(mu) = J_p(mu) + c_p(mu) delta J_q(mu),
c_p(mu)  = a(mu) χ(p).
```

### The two derivative terms that must be retained

[`ScaleDerivativeTransport.lean`](ScaleDerivativeTransport.lean) defines
`differentialPart` as literally the first three terms of the native
`compositeResidual`:

```text
L J = mu ∂_mu J + beta ∂_g J - fieldAction J.
```

Let `eta` denote the zero-extended `(1,1)` delay. For the actual family,
`family_differential_change` proves

```text
L J'_p = L J_p + c_p delta(L J_q)
         + mu c'_p delta J_q
         + 2 c_p betaAction(eta J_q).
```

The last line comes from differentiating `g²`; the preceding extra term
comes from the scale dependence of `a`. Both signs and the factor of two
are checked against the native operators. The proof uses the same beta,
field coefficients, cutoffs, insertion position and independent external
momenta. The derivative identity is established for `0 < mu < UV`, matching
the native scale-smoothness domain. Equality near `mu` justifies taking the
derivative of the positive-scale extension.

There is also a concrete check against dropping the coupling term. Using
the native beta guards, `beta_correction_four_two` proves that its
`g^4 hbar^2` coefficient is

```text
2 c_p beta(3,1) J_q(0,0).
```

`beta_correction_four_two_ne_zero` proves this is nonzero when its three
variable factors are nonzero. Thus even a scale-independent correction can
require a change in mixing. This is a conditional coefficient calculation,
not an evaluation of the unknown constructed theory's beta or insertion.

### Weak residual limits and the remaining construction

[`WeakLocalTransport.lean`](WeakLocalTransport.lean) proves that the actual
`WeakLocalEndpointZero` predicate is preserved under addition, constant
complex scaling and the `(2,1)` delay. Integrability is taken from the
original hypotheses before applying integral linearity; the UV limit is
still taken first at positive IR, followed by the IR limit.

`weakLocal_congr_eventually` also proves that equality only for sufficiently
large UV at each positive IR is enough. This permits identities whose
scale-smoothness proof requires `mu < UV`; it does not require equality at
every finite UV. These closure lemmas will apply **after** the changed
residual has been proved to be the required finite combination of old ones.
That residual identity has not yet been proved.

The next task is to construct native `CompositeMixing` and
`LocalScalePrimitive` data that cancel the displayed product-rule terms and
the mixing induced by the change of labels. Those data must satisfy their
own filtration, unit, linearity, graph-order and smoothness fields. With
`χ(q)=0`, the earlier correction has a finite inverse. In the native
column-label convention, the candidate matrix rule is
`K' = M^-1 K M - M^-1 (mu ∂_mu + beta ∂_g) M`, with
`M = I + hbar g² a(mu) N` and `N(p)=χ(p)q`. This rule is a construction
plan, not a theorem asserted by this audit.

One technical point in that construction is that `CompositeMixing.smooth`
is stated for each fixed output label. It does not by itself justify taking
a derivative of a sum with scale-dependent output support. A possible way
to avoid that step is a fixed invertible label map `p -> p + χ(p)q` when
`χ(q)=0`, using finite differences of reindexed output coefficients and the
linearity of the observable dictionary. This has not yet been implemented.

Beyond this conditional scale-normalization transport, generated coefficient
recovery, physical reconstruction and all-orders continuum matching remain
open, as does construction of the original interacting family from the
available October source. See [ym-lean #27](https://github.com/alxwest/ym-lean/issues/27)
for the broader bridge blocker. No new native existence submission was made.

Reproduce from the YM-ymg checkout:

```sh
python3 integrations/ym-lean/audit/check_scale_derivative_transport.py \
  --ym-lean ../ym-lean \
  --out integrations/ym-lean/runs/scale-derivative-transport-new
```

The output directory must be new. The scoped success status is
`SCOPED_SCALE_DERIVATIVE_TRANSPORT_CHECKED`; the full scale-normalization,
full residual-transport and existence-certificate flags remain false.

## Physical-word transport and complete Ward-family equivalence, 12 November

The finite correction now preserves the two physical-state conditions
left open by the dictionary audit below. **Given an existing native
`LocalWardFlowFamily`, the corrected dictionary belongs to a complete
native `LocalWardFlowFamily` for the same fixed flow system.** If the
correction's lower label has zero weight, the construction has an exact
inverse. This is a proved equivalence of presentations of this structure.

It is still conditional on an original family. It does **not** produce that
family from the October YM-ymg existence theorem, transport the separate
scale-normalization/reconstruction data, or prove equivalence of the full
ym-lean and YM-ymg existence statements. The existence candidate and native
verifier have not changed.

The fresh [80-declaration audit](evidence/physical-word-transport-2026-11-12/result.json)
checks **28 new declarations and 52 dependencies**. Every local dependency
is rebuilt in an isolated output directory against the pinned native target.
The [logs](evidence/physical-word-transport-2026-11-12/) and
[manifest](evidence/physical-word-transport-2026-11-12/manifest.json)
record source and compiled-module hashes. Compilation treats warnings as
errors; the transitive-axiom audit allows only `propext`, `Classical.choice`
and `Quot.sound`. Five audit-log control tests also pass.

### What is transported

Use the same global correction and admissibility hypotheses as below:

```text
O'_p(mu) = O_p(mu) + hbar g² a(mu) χ(p) O_q(mu).
```

[`PhysicalWordTransport.lean`](PhysicalWordTransport.lean) proves:

- `wordMap_native` and `exactWordMap_native` identify the finite algebra
  with the **actual** native `physicalLiftedWordExpansion` and
  `physicalExactInvariantWord`. The original position slots, continuum
  distributions, exact primitive, anomaly map and monomial cutoffs are used.
- `physical_word_null` preserves `InvariantPhysicalNullIdentity`. It uses
  exactly the old identity's domain: invariant spectators, no elementary
  external legs, compact tests and separated insertion supports. It does
  not declare contact terms at coincident insertions to be zero.
- `physical_word_graph` preserves the distributional vanishing condition
  `order < 2 * loop` at every arity, including the empty word.
- `physical_word_null_iff` and `physical_word_graph_iff` give the reverse
  implications when `χ(q)=0`, using the correction with coefficient `-a`.
- `changeFamily` fills **every field** of the native `LocalWardFlowFamily`
  structure. It uses the earlier full Ward-restoration theorem and the two
  new physical-word theorems. The remaining fields use the same continuum,
  connected data, contact counterterms, mollifier and fixed flow system.
- `changeFamily_inverse` proves equality with the original complete family
  after the two opposite corrections. `changeFamilyEquiv` packages the
  construction and inverse as an actual Lean equivalence.

The coefficient `a(mu)` can vary with the normalization scale. These family
conditions are imposed at each scale. This theorem does not infer the
additional smoothness or derivative identities required by the separate
scale-insertion conditions.

### Why the physical-state conditions survive

Taylor coefficients of the correction shift coupling order by two and loop
order by one. Write this operation as `delta`, with zero whenever a shifted
index would be negative. [`WordJetAlgebra.lean`](WordJetAlgebra.lean) proves
that `delta` commutes with finite convolution in either factor and with the
actual finite insertion maps.

Replacing an insertion by its corrected version therefore yields a sum of
original words, with some invariant labels replaced by `q`, multiplied by
finite scalar factors and shifted by `delta`. The proof handles every
position without reordering slots. `wordMap_transfer` formalizes this
argument for any property closed under addition, scalar multiplication and
the shift; `labels_of_slots` verifies that the resulting lists still are
words covered by the original hypotheses.

For the exact-state identity, all resulting original words vanish on the
same permitted test. For graph order, the nonzero shift takes `(r,l)` to
`(r-2,l-1)`, and `r < 2*l` implies `r-2 < 2*(l-1)` when both shifted indices
exist. Boundary cases vanish by the definition of the shift. Neither
argument exchanges a continuum limit with an infinite sum.

### Two directional Legendre fields

[`ChangedFamilyLegendre.lean`](ChangedFamilyLegendre.lean) goes one step
further, **assuming an original `GeneratedScaleNormalization` also exists**.
The native `LegendreFlowAdapters` theorems derive directional compatibility
from the fixed flow equations and the original background Legendre equation.
Applying them to the actual changed family proves the exact
`CompositeCSConditions.lifted_directional` field. The same argument proves
`exact_directional` for any proposed admissible primitive family.

These are applications of the native theorems to the changed data; the
original normalization is not constructed. Selecting primitives and mixing
coefficients that solve the changed scale equation is still required.

### Remaining bridge obligations

This closes the previous **complete changed Ward-family** gap. The next
unproved transport is `GeneratedScaleNormalization.same_scale_insertion`:
the actual `CompositeCSConditions` must hold after differentiating the
changed dictionary in both scale and coupling. Merely retaining the old
mixing coefficients is not justified. The two directional Legendre fields
are now checked under an existing normalization. The changed insertion's
joint scale smoothness and weak UV/IR limits of the computed composite
residual remain unproved, as do the required transformed mixing and
primitive data.

Separately, generated coefficient recovery, physical reconstruction and
all-orders continuum matching remain obligations. The previously computed
Gaussian channel has not been identified with the actual generated mixing
coefficient. Most fundamentally, these conditional transport results do not
construct the original interacting flow family or the missing uniform
remainder bounds from the available October submission. The broader blocker
is tracked in [ym-lean #27](https://github.com/alxwest/ym-lean/issues/27).

Reproduce from the YM-ymg checkout, with the pinned ym-lean dependencies built:

```sh
python3 integrations/ym-lean/audit/check_physical_word_transport.py \
  --ym-lean ../ym-lean \
  --out integrations/ym-lean/runs/physical-word-transport-new
```

The output directory must be new. Success is reported as
`SCOPED_PHYSICAL_WORD_TRANSPORT_CHECKED`; the report explicitly retains
`existence_only_kernel_certificate: false` and
`original_local_ward_flow_family_constructed: false`.

## Global dictionary and insertion-limit transport, 12 November

The finite correction now extends beyond the individual-observable checks
below. **The complete native `QuantumObservableLift.Compatible` and
`QuantumObservableLift.LimitCompatible` structures are preserved.** For an
elementary strictly degree-lowering correction, the native
`FullMultiWardRestoration` proposition holds **if and only if** it held
before the correction. The original action, insertion flows, continuum
data, anomaly maps and contact Ward equations are the same on both sides.

This closes the earlier global dictionary/weak-insertion-limit gap. It does
**not** construct an original interacting flow witness, a complete changed
`LocalWardFlowFamily`, or an accepted existence proof. In particular,
equivalence of this Ward-restoration fragment is not equivalence of the
complete ym-lean and YM-ymg existence statements.

There are **42 new audited declarations**, plus 10 reused Ward-shift
helpers, in the fresh [52-declaration run](evidence/dictionary-renormalization-2026-11-12/result.json).
The [logs](evidence/dictionary-renormalization-2026-11-12/) and
[manifest](evidence/dictionary-renormalization-2026-11-12/manifest.json)
record source hashes and the unchanged native target. Five negative/control
tests for the axiom-log checker also pass. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted.

### The global correction and its inverse

For a lower label `q`, a real linear functional `χ` on **all** invariant
labels, and a real coefficient `a`, define

```text
O'_p = O_p + hbar g² a χ(p) O_q.
```

The same formula defines both finite-cutoff and physical coefficients,
using the entire lower observable at every loop. Its required properties
are explicit: `χ(1)=0`, classically identical labels have equal weights,
and a nonzero `χ(p)` requires `dim(q) ≤ dim(p)`.

[`DictionaryRenormalization.lean`](DictionaryRenormalization.lean) proves:

- `compatible`: every field of the actual native compatibility structure,
  including global linearity, fixed tree normalization, the unit, support,
  coupling smoothness/grading, coefficient limits and all-loop closure.
- `relations_preserved`: the original quantum-exact primitives still prove
  label identities, since related labels receive exactly equal corrections.
- `direction_for_pair`: given the target's actual `FilteredBasis` and any
  two labels `P,q` with `dim(q) < dim(P)`, there exists such a functional
  with `χ(P)=1` and `χ(q)=0`. It uses the basis's actual connection
  coordinates; `P` need not itself be a basis label. A nonzero higher
  coordinate follows from intrinsic degree and finite reconstruction.
- `change_inverse`: if `χ(q)=0`, applying the same construction with `-a`
  recovers the original dictionary exactly, including finite-cutoff data.

Thus a correction of the previously considered form can be extended
consistently to all labels under these explicit hypotheses. Applying it
to the concrete curvature example still requires identifying the actual
labels and their strict intrinsic-degree relation with that calculation.

### Coupling derivatives and the ordered continuum limits

[`CouplingTaylorShift.lean`](CouplingTaylorShift.lean) proves the exact
Taylor identity for a smooth function, with no analyticity assumption:

```text
[g^r](g² f(g)) = 0                  for r < 2,
              = [g^(r−2)]f(g)      for r ≥ 2.
```

Together with the one-loop shift, the correction is a delay by `(2,1)` in
coupling/loop order. Its finite Cauchy convolution is proved directly.

[`DictionaryInsertionTransport.lean`](DictionaryInsertionTransport.lean)
evaluates the **actual** native `finiteInsertion`, `finiteIntegrand`,
`ultravioletInsertion` and `physicalInsertion` definitions. For the last
two, for example,

```text
J'_p(r,l) = J_p(r,l) + a χ(p) J_q(r−2,l−1),
```

where the second term is zero when either shifted order is negative.
The support proof justifies reducing the monomial sum from `p`'s degree
bound to `q`'s; it is not an assumed equality of unrelated cutoffs.
Finite-cutoff coupling derivatives use the existing joint smoothness
condition, and integral addition uses the existing integrability guards.

`limitCompatible` then proves all four native limit fields: joint
coupling/momentum smoothness, compact-test integrability, the positive-IR
UV limit and the subsequent nonexceptional IR limit. The argument uses
finite linearity and the original limits. It does not exchange a limit
with an uncontrolled infinite sum or derivative.

Finally, `fullWardRestoration` preserves the whole native restoration
bundle, and `fullWardRestoration_iff` uses the exact inverse to prove its
logical equivalence before and after the change.

### What remains beyond this theorem

The scalar `a` may be chosen separately at each subtraction scale, so the
previous Gaussian cancelling coefficient is available pointwise. The
complete scale-dependent theory has further conditions:

1. `LocalWardFlowFamily` additionally requires invariant physical-state
   null identities and coupling/loop grading of whole vacuum words. This
   run does not transport those two fields or construct a full new family.
2. `GeneratedScaleNormalization` differentiates the dictionary in the
   subtraction scale and coupling. Its same-flow Callan–Symanzik residual,
   quantum-exact terms, and transformed mixing must still be checked.
   Pointwise Ward compatibility does not supply that equation.
3. The full interacting coefficient/OPE identification, exhaustive physical
   sectors and nonperturbative all-orders remainder estimates are still
   missing. The Gaussian coefficient is not promoted to the complete
   generated physical coefficient by the present structural theorem.

The result therefore establishes that these **dictionary, Ward and weak
insertion-limit requirements** do not by themselves prohibit the finite
correction. It does not decide necessity or consistency of the full target.

Reproduce with a fresh output directory:

```sh
python3 integrations/ym-lean/audit/check_dictionary_renormalization.py \
  --ym-lean ../ym-lean --out integrations/ym-lean/runs/dictionary-new
```

The runner rebuilds all local dependency modules into that directory,
checks the native pin and input hashes before and after compilation, and
requires the exact declaration/axiom sets. Compiled `.olean` files are
rebuildable outputs; the published evidence contains their hashes and the
compiler logs. The success status is
`SCOPED_DICTIONARY_RENORMALIZATION_CHECKED`, with full existence acceptance
and generated scale-normalization transport explicitly false.

The submitted existence theorem and verifier are unchanged. The last
native signature rejection in [ym-lean #27](https://github.com/alxwest/ym-lean/issues/27)
therefore remains unresolved; no new native existence run is claimed.
This result also bears on the separate specification review in
[#26](https://github.com/alxwest/ym-lean/issues/26). No YM-group review of
these new artifacts is claimed.

## Renormalized channel follow-up, 12 November

The Gaussian part of the proposed degree-eight to degree-four test is now
computed, including the subtraction counterterm, its scale derivative, and
the incoming identity terms in the sector comparison. **The full generated
physical Yang–Mills channel and the existence bridge remain unresolved.**

There are **47 new audited Lean declarations** in this follow-up, against
the unchanged Lean 4.32.0 target
`baecbb5eba5710fb707cfaecfaf7365d8feff5f7`:

| File | Checked result | Scope |
| --- | --- | --- |
| [CurvatureVariance.lean](CurvatureVariance.lean) | Exact native complex free-curvature integral and integrability | Four-dimensional finite-cutoff Gaussian covariance, with arbitrary color indices |
| [RenormalizedGaussianChannel.lean](RenormalizedGaussianChannel.lean) | Color combinatorics, subtraction, conditional ODE uniqueness, scale derivative and cancellation | Renormalized Gaussian channel; the reduction of the full insertion flow is not proved |
| [RenormalizedSectorPairing.lean](RenormalizedSectorPairing.lean) | Actual native stripping with both incoming identity terms; nonzero sector difference | Conditional two/three-label Frame slices, not an exhaustive generated physical sector |
| [QuantumClosureShift.lean](QuantumClosureShift.lean) | Finite correction preserves the same generated Ward equation at every loop, coupling grading and dimension bounds | Individual corrected representatives; not a complete transformed observable dictionary or flow family |

The [result JSON](evidence/renormalized-channel-2026-11-12/result.json),
[axiom logs](evidence/renormalized-channel-2026-11-12/), and
[manifest](evidence/renormalized-channel-2026-11-12/manifest.json) record the
checked sources. Success uses only `propext`, `Classical.choice` and
`Quot.sound`. It is not native existence acceptance.

### The calculation

Write `n` for the number of color components, `X_a` for the linearized
`F₀₁` component, `Q = Σ_a X_a²`, and `P = Q²`. The corresponding source
normalizations start at `g² Q` and `g⁴ P`. This notation isolates the
Gaussian component; it does not replace nonlinear curvature with a free
field in the full Yang–Mills theory.

1. The exact imported covariance gives

   ```text
   v(Λ, UV) = ∫ (p₀²+p₁²) C(Λ,UV;p) / (2π)⁴ dp
            = (UV⁴−Λ⁴)/(32π²).
   ```

   This is now a Lean proof of the actual complex contraction integrand's
   integral, including its color Kronecker delta and integrability. It uses
   Cartesian Gaussian products and measure-preserving coordinate swaps;
   no angular-average formula or numerical quadrature is assumed.

2. The Gaussian generator satisfies

   ```text
   (½Δ)Q = n,        (½Δ)P = 2(n+2)Q.
   ```

   Subtracting at `Λ=μ` gives the lower-degree coefficient

   ```text
   a(μ,Λ) = 2(n+2)[v(Λ,UV)−v(μ,UV)]
          = (n+2)(μ⁴−Λ⁴)/(16π²).
   ```

   The UV cutoff cancels, and `a(μ,μ)=0`, as required by the lower-output
   normalization. The derivative is `∂Λ a = −(n+2)Λ³/(4π²)`.
   `quarticShift_unique` proves that this is the unique continuous solution
   with that derivative and subtraction boundary on the positive-cutoff
   interval. **Identifying the actual insertion-flow right-hand side with
   this derivative remains a hypothesis of that theorem.** The graph-count
   lemma excludes cubic/quartic interaction vertices in a four-field to
   two-field one-loop graph under its explicit counting identities; the
   native flow-to-graph identification is not supplied by the count alone.

3. In the convention `μ ∂μ O = −γ O`, the Gaussian coefficient of the
   relative `g²` mixing from `P` to `Q` is

   ```text
   γ₂(μ) = −(n+2)μ⁴/(4π²),
   ```

   which is nonzero for positive `μ`. The sign follows the native
   `compositeResidual` convention. This value is **not** asserted to equal
   `GeneratedScaleNormalization.euclideanGammaLoop` for a complete native
   physical prescription.

### Identity mixing does not cancel the sector difference

The full Gaussian change on `(1,Q,P)` has columns

```text
S(s) = [ 1   n s   n(n+2)s² ]
       [ 0    1    2(n+2)s  ]
       [ 0    0       1     ],       S(s) S(t) = S(s+t).
```

Here `s` is the covariance-change parameter in the chosen normalization;
for source-normalized fields it includes the corresponding coupling
factor. With transport `S(−d)`, the native `strippedMultiPairing` yields

```text
three labels:  λ⁴ [low − 4 d unit]
two labels:    λ⁴ [low + 2 n d unit]
difference:  −2(n+2) λ⁴ d unit.
```

`low` and `unit` denote the respective distributions evaluated on the same
dilated test. Both `1·Q -> Q` and `Q·1 -> Q` incoming terms are included.
The unknown `Q·Q -> Q` coefficient cancels in the difference. The
`Q·Q -> 1` coefficient cannot reach the tested `Q` output under this
downward transport. The supplied channel table and Frame identifications
are still explicit hypotheses: this is not an identification with the
complete, exhaustive physical OPE basis.

### A finite correction removes this Gaussian mixing

At leading loop order, replace the representative by

```text
O'_P = O_P + hbar g² α(μ) O_Q,
α(μ) = −a(μ,0) = −(n+2)μ⁴/(16π²).
```

Then `γ'₂ = γ₂ − μ α'(μ) = 0`, proved by `corrected_gamma`. On the complete
three-dimensional Gaussian polynomial space, the finite correction
`S(d)` cancels `S(−d)` exactly, including the double-contraction unit term.
This addresses the Gaussian obstruction; it does not claim that all other
degree-lowering mixing in Yang–Mills disappears.

Using the **entire** corrected lower observable extends the local Ward
check beyond one loop: `shifted_closed` proves that
`O_p + hbar g² α O_q` obeys the same generated Ward equation at every
loop whenever the original representatives do. `shifted_graph_grading`
and `shifted_support` prove the corresponding coupling and support guards.
The theorem checks an individual pair of labels. It does not construct a
global linear map respecting all identities on connections, the unit,
the UV/IR insertion limits, the physical dictionary, or the transformed
Callan–Symanzik normalization. Those are additional native requirements.

Thus the calculated nonzero term is **prescription dependent in the
Gaussian sector**. Neither the term nor the sector discrepancy proves an
unavoidable obstruction for every realization allowed by the existential
target. Conversely, cancelling it does not prove that every extra
condition in that target follows from Jaffe–Witten.

### Remaining blocker and reproduction

To finish this test as a statement about the full target requires a
same-prescription bridge from the actual normalized insertion flows and
quantum-exact terms to this calculation, a complete allowed change of
dictionary if the correction is used, and the corresponding generated OPE
and running Frame in the exhaustive basis. Even that would not supply the
missing nonperturbative all-orders remainder estimates in the original
existence bridge. No such theorem has been proved here, and no axiom or
admission-rule change replaces it.

Reproduce the new check with a fresh output directory:

```sh
python3 integrations/ym-lean/audit/check_renormalized_channel.py \
  --ym-lean ../ym-lean --out integrations/ym-lean/runs/renormalized-new
```

The runner also executes five audit-log controls and
[independent_renormalized.py](independent_renormalized.py). The latter uses
exact rational Gaussian moments for 1, 3, 8 and 15 color components and
evaluates every matrix index in the two/three-label contraction. These are
independent finite checks, not realizations of the complete gauge theory.

The native target and submitted existence theorem are unchanged, so the
native existence verifier was not rerun. The last rejection remains
`INCOMPATIBLE_PROOF_SIGNATURE`, with submitted type
`YMGBridge.PresentedJointExistence.{u}` instead of
`YangMills.YangMillsExistenceOnly.{u}`; the translation is still unproved.
This supplements [ym-lean #27](https://github.com/alxwest/ym-lean/issues/27)
and the separate specification review
[#26](https://github.com/alxwest/ym-lean/issues/26). No review of these new
artifacts by the YM group is claimed.

## Earlier requirement checks, 12 November

The new checks validate several parts of the encoding, but **do not establish
that every additional condition in ym-lean is necessary for Jaffe–Witten**.
They also do not establish a physical counterexample to the target. The
tests concern logical and mathematical content, not the people involved.

The target remains the unchanged `alxwest/ym-lean` revision
`baecbb5eba5710fb707cfaecfaf7365d8feff5f7`, using Lean 4.32.0.
The [recorded results](evidence/requirements-2026-11-12/result.json),
[axiom logs](evidence/requirements-2026-11-12/), and
[input-hash manifest](evidence/requirements-2026-11-12/manifest.json)
identify the tested implementation and the exact scope of success.

| Test | Result | What this establishes |
| --- | --- | --- |
| Reorder every label consistently | Pass, seven audited declarations | The actual `Frame`, its RG equation, stripping, locality and all-order bounds transport under any permutation. Matching holds **if and only if** it held before reordering. |
| Four- and six-leg Gaussian coefficients, including fermionic signs | Pass | The actual native Wick engine gives `3 v²` and `15 v³` for repeated bosonic legs. The public vacuum-normalized bare coefficient agrees at order zero, retaining its integrability hypotheses. |
| Free curvature kernel and cutoff derivative | Pass | The imported propagator gives the expected color-diagonal `F₀₁` kernel. Its scale derivative equals the imported flow kernel, including the zero-momentum branch. |
| Gaussian subtraction and change of subtraction | Pass | The exact subtraction coefficients are `-6` and `3`; changing the subtraction can produce a lower-degree term. This is Gaussian algebra, not the generated physical YM mixing coefficient. |
| Reduce the actual generated RG series at its first possible orders | Pass, five audited declarations | Beta coefficients below `g³` and mixing coefficients below `g²` vanish. The `g³` beta and `g²` mixing terms reduce to their actual one-loop components. Their nonzero numerical values have **not** been computed. |
| Full generated degree-eight to degree-four sector calculation | Unresolved | No same-flow, Ward-compatible physical mixing coefficient and corresponding OPE channel have been identified that settle the proposed truncation objection. |

There are **25 new audited Lean declarations** in
[`BasisConsistency.lean`](BasisConsistency.lean),
[`KernelCoefficients.lean`](KernelCoefficients.lean),
[`CutoffDerivative.lean`](CutoffDerivative.lean), and
[`GeneratedOrders.lean`](GeneratedOrders.lean).
Reordering is a restricted basis test: this does not claim invariance under
every filtered basis change or finite renormalization of the full candidate.

### Independent calculation

[`independent_coefficients.py`](independent_coefficients.py) obtains the
Gaussian moments from `exp(v t²/2)`, independently of the native recursive
Wick pairing algorithm. Solving the two cancellation equations for
`X⁴ + a v X² + b v²` gives `a=-6`, `b=3`, agreeing with the checked native
identities. The fermionic four-leg identity has signs `+,-,+`.

The formally checked free curvature integrand is

```text
δ_ab (p₀² + p₁²) C(IR, UV; p) / (2π)⁴.
```

Using the angular average `1/2` and sphere area `2π²` in four dimensions
reduces its coincident covariance to

```text
(1 / (16π²)) ∫₀∞ r³ (exp(-r²/UV²) - exp(-r²/IR²)) dr
  = (UV⁴ - IR⁴) / (32π²).
```

Four numerical checks, including equal cutoffs, agree within `10⁻¹⁰` at
two integration resolutions. The angular reduction and numerical integral
are **not Lean proofs**; the exact native integrand and cutoff derivative
are. This is the free component of curvature at finite cutoffs, not the
full nonlinear gauge-invariant observable or its physical continuum limit.
The regulator and covariance conventions were checked against
[Fröb–Holland, §2, equations (2.13)–(2.17)](https://arxiv.org/pdf/1603.08012#page=11),
in Feynman gauge and the paper's redefined auxiliary-field convention.

### What stopped the decisive sector calculation

The previous finite-sector counterexample below establishes that downward
filtration and overlap agreement alone do not justify truncating before
transport. It does not identify an actual generated physical coefficient.
The follow-up pursued the suggested curvature/Wick channel and found:

1. The actual free curvature kernel and Wick combinatorics can be computed,
   as above. They do not determine the renormalized operator mixing.
2. The target's actual
   [`SingleInsertionBoundaryConditions.normalized`](https://github.com/alxwest/ym-lean/blob/baecbb5eba5710fb707cfaecfaf7365d8feff5f7/YangMills/CompositeExtraction.lean#L305-L329)
   sets every strictly lower-output projector to zero at the subtraction
   point. `normalized_lower_output_zero` proves this directly. Substituting
   a bare contraction for that coefficient would bypass the counterterms.
   This vanishing at one point does **not** imply vanishing scale dependence.
3. The Gaussian identity
   `H₄(v) = H₄(w) + 6(w-v)H₂(w) + 3(w-v)²`
   shows explicitly why changes of subtraction can still mix degrees.
   Promoting this to the physical YM channel requires the corrected
   observable dictionary, actual insertion flow, generated quantum-exact
   terms, and the same-scale Callan–Symanzik equation.
4. `GeneratedOrders.lean` reduces the disputed leading mixing in
   [`GeneratedScaleNormalization`](https://github.com/alxwest/ym-lean/blob/baecbb5eba5710fb707cfaecfaf7365d8feff5f7/YangMills/GeneratedScaleNormalization.lean#L33-L73) to
   `N.euclideanGammaLoop basis mu 2 1 output input`. It does not supply that
   value. The conventional `betaTwoLoop` polynomial is not substituted for
   the actual `GeneratedScaleNormalization.betaSeries` either.

The inspected `FixedFlowSystem` and `GeneratedScaleNormalization` structures
specify these equations and conditions. They are not a completed numerical
instance of the generated physical coefficient system. The available source
finite-cutoff expansions likewise do not identify the above native
renormalized channel. A complete calculation must identify its high-output
coefficient, its downward transport, and any cancelling retained-output
terms in one prescription, satisfying the actual
[`CompositeCSConditions`](https://github.com/alxwest/ym-lean/blob/baecbb5eba5710fb707cfaecfaf7365d8feff5f7/YangMills/CohomologicalScaleInsertion.lean#L286-L312).
A nonzero bare contraction, by itself, would not
resolve that calculation.

The next decisive test is therefore precise: compute that one-loop physical
mixing/OPE channel and compare the two finite-sector stripping expressions.
A contradiction for every allowed realization would refute the target;
a mismatch in one chosen prescription would still require checking whether
an admissible change of prescription removes it. Passing this channel would
not prove that every condition of the full target follows from Jaffe–Witten.

The [earlier scalar limit obstruction](NonuniformLimit.lean) separately
rules out promoting finite-cutoff all-orders asymptotics using just
pointwise convergence and a matching leading term. That is an objective
failed implication, but its scalar example does not decide implication
between the complete Yang–Mills existence statements.

### Reproduce the new checks

From the YM-ymg repository, with the pinned ym-lean dependencies built:

```sh
python3 integrations/ym-lean/audit/check_requirement_audit.py \
  --ym-lean ../ym-lean --out integrations/ym-lean/runs/requirements-new
python3 integrations/ym-lean/audit/test_requirement_audit.py
```

Use a fresh output directory. The runner checks the native pin and source
hashes before and after compilation, requires the exact audit declaration
sets, and permits only `propext`, `Classical.choice`, and `Quot.sound`.
Its success status is `SCOPED_REQUIREMENT_AUDITS_CHECKED`; the JSON explicitly
keeps existence acceptance, a full countermodel, a computed physical mixing
coefficient, and necessity of the whole target **false**.

These checks supplement the current rejection recorded in
[ym-lean #27](https://github.com/alxwest/ym-lean/issues/27), and bear on the
separate specification review in
[#26](https://github.com/alxwest/ym-lean/issues/26). They do not change either
the source theorem's type or the native admission result. No new review of
these audit artifacts by the YM group is claimed.

## Earlier filtered-sector truncation diagnostic

**Scope: checked finite algebra and an explicit asymptotic tail. Not an
existence proof, not a full generated-Yang--Mills countermodel, and not a
proof that the active existence target is inconsistent.**

Historical target inspected: `alxwest/ym-lean@3bc0411516ae9fb01e6992106f4bac122b5af897`,
Lean 4.31.0. Those recorded results remain historical. The current runner
uses the updated parent `pin.json` (Lean 4.32.0); the inspected
`FilteredQuantumRG.lean` definitions are unchanged between these pins.
No target or verifier file is changed. The diagnostic imports
`YangMills.FilteredQuantumRG` and evaluates its actual `strippedMultiPairing`.

## The precise issue

`GeneratedMatching.coefficient_matching` imposes matching in every finite
engineering-dimension sector. `strippedMultiPairing` sums its outgoing
coefficient index over that same sector. The frame permits downward mixing:
an operator of larger engineering dimension can contribute to a smaller
output under transport.

If P projects to a small sector and R is downward filtered, preservation of
the small **input** subspace does not imply P R = R_small P. Higher outputs
of an OPE can feed a retained output after transport. Agreement of all
matrix entries on overlapping sectors does not remove those contributions.
This is a specific question about truncation before transport, not a demand
for a generic new framework-equivalence theorem.

## What is proved

Use three labels with intended degrees (0,4,8), indexed (0,1,2), and

    R_a(v)_1 = v_1 + a v_2,   R_a(v)_0 = v_0,   R_a(v)_2 = v_2.

`shear` is an explicit linear equivalence with inverse obtained by replacing
a by -a. `shear_filtered` proves the one-sided dimension filtration;
`shear_overlap` proves that all entries in the first two indices agree with
identity transport. `projection_shear_failure` is an **unconditional**
finite-dimensional counterexample to commuting projection with this shear.

For the isolated coefficient channel C_(1,1)^2 = L:

- `restricted_stripped_zero` evaluates the actual two-label stripping to 0.
- `shear_stripped` evaluates the actual three-label stripping, at output 1,
  to lambda^4 a, when L on the dilated test is 1.
- `finite_sector_discrepancy` proves these are unequal for nonzero lambda
  and a. These statements explicitly assume the relevant transport slice
  of a Frame; they do not construct a generated physical Frame.

The difference need not be beyond all perturbative orders. Set

    q(t) = 1/(1+2t),  lambda = exp(-t),
    a(t) = exp(4t) q(t) - 1.

Here q is the scalar profile g^2 for g(t)=(1+2t)^(-1/2), for t>=0; this
notation does not instantiate the target's RunningCoupling structure.
The profile starts at zero and its proved derivative is
exp(4t)(4q-2q^2). The imported stripping formula then has tail

    lambda^4 a(t) = q(t) - exp(-4t).

`active_stripped_tail` connects this equality to the actual target formula.
`tailRatio_limit` proves tail/q -> 1, and `tail_not_flat` proves that the
bound |tail| <= epsilon q cannot hold eventually for every epsilon>0.
Thus this diagnostic tail already matters at the g^2 order; filtration by
itself does not justify discarding it in an all-order comparison.

## What is NOT proved

The diagnostic coefficient table is not asserted to be the output of the
fixed YM flow. No exhaustive actual-G basis, full RunningCoupling/Frame,
Ward-restored engine, physical OPE, or Wightman model realizing the example
has been constructed here. A specific matrix-entry trajectory and a scalar
asymptotic calculation are not replacements for those proof obligations.

Consequently this does not prove that a `FilteredExistenceCandidate` cannot
exist, or that a source-admissible YM realization must encounter this tail.
The simultaneous generated constraints could eliminate the example or admit
an appropriate special presentation. That remaining question must be tested,
not inferred from the finite counterexample.

A targeted next test is the fixed positive-subtraction-scale Wick channel
for a quadratic curvature observable and its square. The required calculation
must identify the higher-output OPE coefficient, its generated downward
mixing, and the resulting lower-output term in identical conventions. Merely
citing the usual existence of finite operator mixing is insufficient.

No speculative repair is made: imposing homogeneous transport could add an
unjustified restriction, and adding an infinite outgoing sum would require
its own definition and convergence/tail control.

## Reproduce

With the pinned trusted target and its dependencies built:

```sh
python3 integrations/ym-lean/audit/check_filtered_sector.py \
  --ym-lean /path/to/pinned/ym-lean --out /path/to/new/audit-run
```

The script checks the target revision, tracked cleanliness, pinned verifier
hashes and toolchain before and after compiling. It requires every named
axiom audit and rejects anything beyond `propext`, `Classical.choice` and
`Quot.sound`. Exit 0 means **only this diagnostic passed**. Its JSON always
keeps `existence_only_kernel_certificate=false` and
`full_generated_countermodel_constructed=false`.

The separate unchanged native admission command remains in the parent
README. A supplementary diagnostic does not create or submit an existence
proof. The checked run is recorded in `evidence/`.
