# Filtered-sector truncation diagnostic

**Scope: checked finite algebra and an explicit asymptotic tail. Not an
existence proof, not a full generated-Yang--Mills countermodel, and not a
proof that the active existence target is inconsistent.**

Target inspected: `alxwest/ym-lean@3bc0411516ae9fb01e6992106f4bac122b5af897`,
Lean 4.31.0. No target or verifier file is changed. The diagnostic imports
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
