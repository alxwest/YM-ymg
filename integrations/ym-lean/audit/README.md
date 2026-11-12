# Checks of extra ym-lean requirements

## Results of the 12 November follow-up

The new checks validate several parts of the encoding, but **do not establish
that every additional condition in ym-lean is necessary for Jaffe–Witten**.
They also do not establish a physical counterexample to the target. The
tests concern logical and mathematical content, not the people involved.

The target remains the unchanged `alxwest/ym-lean` revision
`baecbb5eba5710fb707cfaecfaf7365d8feff5f7`, using Lean 4.32.0.

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
2. The target's actual `SingleInsertionBoundaryConditions.normalized`
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
4. `GeneratedOrders.lean` reduces the disputed leading mixing to
   `N.euclideanGammaLoop basis mu 2 1 output input`. It does not supply that
   value. The conventional `betaTwoLoop` polynomial is not substituted for
   the actual `GeneratedScaleNormalization.betaSeries` either.

The inspected `FixedFlowSystem` and `GeneratedScaleNormalization` structures
specify these equations and conditions. They are not a completed numerical
instance of the generated physical coefficient system. The available source
finite-cutoff expansions likewise do not identify the above native
renormalized channel. A complete calculation must identify its high-output
coefficient, its downward transport, and any cancelling retained-output
terms in one prescription. A nonzero bare contraction, by itself, would not
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
