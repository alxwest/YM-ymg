# Checks of extra ym-lean requirements

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
