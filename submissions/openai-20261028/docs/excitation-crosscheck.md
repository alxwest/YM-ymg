# Gap-free centered-trace excitation: a supplementary October cross-check

This is an **additional Lean consequence** of the October submission's public
Wightman axioms and its `Hierarchy` interface. It is not part of the
historical A1–A8 package or the existing Comparator endpoints, and does not
modify any file of the preserved `submission/` distribution.

## Checked implications

The new [ExcitationFromPublic.lean](../checks/ExcitationFromPublic.lean)
contains two theorems:

1. `YangMills.WightmanTheory.hasFieldExcitation_of_centered_nonzero`:
   in the *actual* normalized and cyclic Wightman field system, a field
   with vanishing vacuum one-point function whose smeared operator is
   nonzero creates a field word outside the vacuum line.
2. `YangMills.Hierarchy.nonvacuum_of_reconstructed_nonzero_trace`:
   a `Hierarchy.Reconstructed` together with its `TraceTest` and
   `centeredTrace ≠ 0` implies that its very Wightman theory has such
   an excitation. Injectivity of `toLabel` and field faithfulness are used.
   No second Hilbert space or state is introduced.

This is stronger than the public
[`Reconstructed.acts`](../submission/ChallengeSpec.lean) condition, which
could also be satisfied by the nonzero identity operator.

**The explicit nonzero-trace-field hypothesis has NOT been eliminated from
the second theorem in this supplementary check.** The submitted construction
has a related `TraceExtension.nonzero_strength` result used by
[`NonzeroPhysicalObservable.probe_from_trace`](../checks/NonzeroPhysicalObservable.lean).
The final Lean term applying that internal result to the exact same public
`hierarchy F Q` has not yet been added here.

No mass gap, intrinsic positive mass, uniqueness of infinite-volume limit,
or all-orders perturbative coefficient matching is claimed.

## Reproduce independently (Lean 4.32.0)

Use the **original** October submission checkout and its pinned dependency
cache. From `submissions/openai-20261028/submission/`:

```sh
lake exe cache get
lake build ChallengeSpec
lake env lean -R ../checks -DautoImplicit=false -DwarningAsError=true \
  -o .lake/build/lib/lean/ExcitationFromPublic.olean \
  ../checks/ExcitationFromPublic.lean
lake env lean -R ../checks -DautoImplicit=false -DwarningAsError=true \
  ../checks/ExcitationFromPublicAudit.lean
```

The separate [audit](../checks/ExcitationFromPublicAudit.lean) prints
transitive axioms of both theorems. On 11 November 2026 on `ym-runner-2`
both checks compiled without errors or warnings; the axiom sets contained
only `propext`, `Classical.choice`, and `Quot.sound`.

## Relationship to the other specification

This source-native lemma is part of the same gap-free comparison tracked by
[alxwest/ym-lean issue #8](https://github.com/alxwest/ym-lean/issues/8)
and [the target-side PR #11](https://github.com/alxwest/ym-lean/pull/11).
The `ym-lean` theorem has a closely analogous mathematical conclusion.
Neither source nor target currently contains a kernel-checked
cross-repository transport from the selected source Hilbert space, fields
and full vacuum kernels into `FilteredExistenceCandidate` or even the
partial `ExistenceKinematics` type.

The remaining main obstacles are a common Lean/Mathlib build or verified
definitional interface, target-side finite component fields, self-adjoint
full-domain time generator, separability, full joint-Schwartz vacuum
kernels, and fixed group-dependent perturbative YM identification.
