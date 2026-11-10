import CompletenessAudit

/-!
# [A2] What “complete operator content” checks — 28 October 2026

This example separates four assertions which are easily conflated:
exhaustion of polynomial labels, the size of the correlation-null quotient,
preservation of that quotient in each phase, and density of field words in the
reconstructed Hilbert space. They are the assertions assembled in
`AcceptanceSpec.OperatorContent`. None is a comparison with a separately
constructed canonical Yang–Mills Hilbert space.

The labels are algebraic local-field labels, not bounded operators on the
Hilbert space. Their degree is a filtration bound. The passage through
correlations and reconstruction is needed to obtain smeared field operators.
All theorems below are consequences of the existing review audit.
-/

set_option autoImplicit false
noncomputable section
namespace YMReview.Examples.OperatorContent
open YM
open scoped Topology
variable {G : Gauge}

/-!
## 1. Is the raw register exhausted?

`Labels.Pol G` is the submitted polynomial label space and
`Labels.invariantSpace G` is its invariant subspace. A label in
`Labels.Label G d` has a finite weight bound d. Every invariant polynomial
has finite support, so taking the maximum monomial weight places it at some
register level. No fixed upper degree is imposed on the full collection.

This is exhaustiveness relative to the submitted algebraic dictionary. Human
review must still identify that dictionary with the intended local gauge-
invariant fields. The theorem alone does not establish completeness for every
nonlocal observable, such as an independently specified class of line defects.
-/

theorem every_registered_polynomial_appears (p : Labels.Pol G)
    (hp : p ∈ Labels.invariantSpace G) :
    ∃ d : ℕ, ∃ v : Labels.Label G d, v.val = p :=
  OperatorCompleteness.raw_register_exhaustive p hp

/-!
## 2. The free on-shell comparison is itself substantive

`Maxwell.shellSector G d` is the free on-shell polynomial comparison space
at filtration d. The first theorem identifies it with the invariant part of
the free lower-weight cap. The second states that its separated correlations
leave no further residual null space. These identify the comparison space;
they are not claims that interacting correlation functions are Gaussian.
-/

theorem free_sector_dictionary (d : ℕ) (p : Maxwell.WickPol G) :
    p ∈ Maxwell.shellSector G d ↔
      p ∈ Maxwell.Free.lowerCap G d ∧
        ∀ u : G.El, Maxwell.Free.pigment u p = p :=
  OperatorCompleteness.free_sector_exhaustive d p

theorem free_residual_vanishes (d : ℕ) : Maxwell.residual G d = ⊥ :=
  OperatorCompleteness.free_no_extra_nulls d

variable {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-!
## 3. What is the interacting field space?

In `YM/Euclid/Null.lean`, `S.null d` is the kernel of the map taking a raw
label to all its separated spectator correlations. `S.Field d` is the
quotient by this space. Injectivity of the induced correlation map follows
from taking that quotient; by itself it cannot say that too many fields have
been killed.

The substantive additional result is the submitted rank comparison, reached
through `F.phase.transport.comparator`. Combined with the free quotient
theorems, it gives the complex linear equivalence displayed below. This
constrains the size of the interacting quotient at every filtration level.
The source comparison also tracks its real signed-coordinate structure;
the review consequence below deliberately displays just the linear content.

An equivalence of these vector spaces is not an equality of interacting and
free correlators, an algebra isomorphism, or a unitary equivalence of QFTs.
-/

include F in
theorem interacting_field_dictionary (d : ℕ) :
    Nonempty (S.Field d ≃ₗ[ℂ] ↥(Maxwell.shellSector G d)) :=
  OperatorCompleteness.local_field_content F d

/-!
## 4. Does selecting a phase lose fields?

`F.phase.phase.retains i d` states equality of the phase and mixed null spaces.
The audit transports the preceding equivalence through that equality. The
quantifier is every character phase i, not merely almost every phase under
the decomposition measure. This is stronger than saying that the mixed
correlation function is the average of its phase values.
-/

theorem each_phase_retains_the_dictionary (i : F.α.space.X) (d : ℕ) :
    Nonempty ((F.α.ensemble i).Field d ≃ₗ[ℂ] ↥(Maxwell.shellSector G d)) :=
  OperatorCompleteness.phase_field_content F i d

/-!
## 5. From fields to the reconstructed Hilbert space

`F.action.operators.vector` assigns a Hilbert-space vector to a registered
field word applied to the vacuum. The linear span of its entire range is
dense. It is important that this uses the full field collection: the bridge
for repeated stress traces in [A1] is a smaller observable family and does
not by itself prove this cyclicity statement.

The final theorem is a different assertion: each nonzero local quotient
field has some nonzero smeared operator. Thus passing to the reconstructed
operator representation does not kill a surviving local field class.
It does not assert that every smearing of a nonzero field is nonzero.
-/

theorem full_word_domain_is_dense :
    Dense ((Submodule.span ℂ (Set.range F.action.operators.vector) :
      Submodule ℂ F.action.operators.H) : Set F.action.operators.H) :=
  OperatorCompleteness.registered_words_dense F

theorem surviving_field_has_nonzero_operator (p : S.Union) (hp : p ≠ 0) :
    ∃ f : Boundary.Test4, F.action.operators.field p f ≠ 0 :=
  OperatorCompleteness.quotient_fields_not_lost F p hp

/-!
## Reading these results together

These checks do not restrict the generating family to the C-even stress
trace. They address the full registered invariant collection. They do not,
however, supply an independently checked charge-conjugation-equivariant
dictionary or a classification of C-odd particles. Such assertions would
need their own precise statements.

Likewise, cyclicity is partly a feature of reconstructing a Hilbert space
from field words. Its physical force here comes from using it together with
the field-content comparison and the faithful representation, not from
relabeling that constructed space as an independently defined canonical one.
-/

#print axioms every_registered_polynomial_appears
#print axioms free_sector_dictionary
#print axioms free_residual_vanishes
#print axioms interacting_field_dictionary
#print axioms each_phase_retains_the_dictionary
#print axioms full_word_domain_is_dense
#print axioms surviving_field_has_nonzero_operator
end YMReview.Examples.OperatorContent
