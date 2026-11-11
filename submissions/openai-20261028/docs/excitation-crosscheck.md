# A checked non-vacuum consequence of the constructed centered trace

This is a **supplementary consequence of results already present in the
October submission**, not a correction to its proof or an independent
Yang–Mills construction. It makes the non-vacuum conclusion explicit in a
form useful for comparing another formal specification.

## The connection now checked

[ExcitationFromConstructed.lean](../checks/ExcitationFromConstructed.lean)
uses the original source's actual `YM.Spec.Final C p S` and its selected
physical theory `YangMills.view F.action`. Its two theorems are:

- `selected_nonvacuum_of_positive_trace`: the selected physical Wightman
  theory has a field-generated state outside the vacuum line.
- `selected_constructed_word_outside_vacuum`: that state is literally
  `F.action.operators.vector word` in the original Hilbert space, outside
  the complex span of `F.action.operators.vacuum`.

Their exact analytic premises are `0 < A` and
`YM.TraceExtension.EuclideanAsymptotic F A`: the positive short-distance
trace limit used in the original construction. There is **no independent
nonzero-trace-field premise** and no second theory or selected phase.

The proof uses only the original source results:

1. `nonzero_strength F hA hshort` gives a nonzero **actual trace label**.
2. `F.realization.qt.faithful` gives a nonzero smeared operator of that label.
3. `pinned_centered F` gives its actual zero vacuum expectation.
4. `view_axioms F.action F.realization.qt` supplies the source Wightman
   axioms for the same fields and state space.
5. The already checked general cyclicity lemma gives the non-vacuum word;
   `PublicView.vector_eq` identifies it with the original constructed word.

Thus the explicit nonzero-field assumption in the earlier public-hierarchy
lemma is discharged by the source's own trace result. The global existence
construction is **not reproved by this corollary**: its final object and
positive trace asymptotic remain the original construction's inputs.

## What this does, and does not, establish

`Reconstructed.acts` alone means only that some field operator is nonzero;
the identity operator would satisfy that condition. The original submission
also contains much stronger trace and faithfulness results. This addition
packages a consequence of those results; it is **not evidence that the
original authors omitted a necessary mathematical argument**.

No mass gap, nonzero spectral threshold, uniqueness of phase or thermodynamic
limit, all-orders perturbative matching, or equivalence to `ym-lean` is
asserted. The proof does not replace the original field system or use the
mixed lattice-limit state in place of the selected physical state.

[ExcitationFromPublic.lean](../checks/ExcitationFromPublic.lean) retains the
general and public-hierarchy lemmas. The new constructed-theory corollary
uses the actual `Final` directly, avoiding the unrelated, large import graph
of `HeadlineSpec` and `TraceBridge`.

## Reproduce (original pinned Lean 4.32.0)

From `submissions/openai-20261028/`, with Elan on `PATH` and the dependency
cache available:

```sh
python3 scripts/verify_excitation.py --threads 3
```

The dedicated runner:

- checks the original package hashes before and after;
- builds only `ChallengeSpec`, `PublicView`, and
  `YM.TraceExtension.Sundial.Grand` with their real dependencies;
- compiles all four supplementary modules into **fresh** object files,
  treating warnings as errors;
- checks every expected axiom report and rejects any additional axiom.

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The runner records commands, input hashes, logs, exact declaration types,
and pass/fail status in a new directory under `runs/excitation-*`.
The audit modules are [public](../checks/ExcitationFromPublicAudit.lean)
and [constructed](../checks/ExcitationFromConstructedAudit.lean).

This is not a fresh replay of the full global construction or Comparator.
Historical A1–A8 results and verification inputs remain unchanged. In
particular, the original hashed `docs/checks.md` is preserved verbatim;
this supplement lives outside that historical manifest.

## Relation to ym-lean

This supplies a source-native consequence for
[ym-lean issue #8](https://github.com/alxwest/ym-lean/issues/8) and
[PR #11](https://github.com/alxwest/ym-lean/pull/11).
The cross-repository field representation, full physical kernel identity,
Hamiltonian-generator, and generated Yang–Mills matching obligations are
separate. No complete `FilteredExistenceCandidate` has been constructed by
this addition.

A suitable description for reviewers is: **an explicitly checked consequence
of the original positive trace asymptotic, exposing a genuine non-vacuum
field word in the original selected theory.**
