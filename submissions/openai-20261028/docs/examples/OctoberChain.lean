-- SPDX-License-Identifier: Apache-2.0
import AcceptanceSpec

/-!
# OctoberChain: following the accepted construction through its interfaces

This walkthrough concerns the OpenAI submission of 28 October 2026. It makes
seven consequences of the existing review specification explicit. The lemma
statements and proof terms are unchanged from the earlier local OctoberChain
audit; the additional material here explains how to read them.

The route is

  local lattice sections → renormalized insertions → mixed continuum hierarchy
    → characters of the ground-state algebra → selected relativistic theory.

There are several different claims along this route. A formula for an insertion
is an equality of definitions. A continuum-limit theorem is a convergence
statement. A phase certificate identifies states through an operator algebra.
A reconstruction certificate identifies vacuum expectations. Read each lemma's
hypotheses before treating these as one undifferentiated existence assertion.

## What the parameters mean

* `C : Family G` contains a Wilson lattice family, its spacing and volume
  schedule, local sections, and renormalization data.
* `N` indexes lattice refinement and `p` physical volume. Increasing `N` at
  fixed `p` removes the ultraviolet cutoff at fixed physical side length.
* `o : Extraction.Order` records the chosen extraction order. The accepted
  limit uses the full UV sequence and the volume subsequence `o.per`.
* `S : Table C.book` is the unselected, possibly mixed continuum hierarchy.
* `F : Spec.Final C o S` retains the fields, stress tensor, phase construction,
  analytic continuation and relativistic reconstruction associated with them.
* `Acceptance.Accepted hg F` adds the explicitly stated review requirements
  for this same `F`, including the finite Wilson law and full-UV convergence.

`AcceptanceSpec` supplies definitions, not an assumed existence axiom. The
separate theorem `YMReview.Acceptance.combined_acceptance` in
`checks/CombinedAcceptance.lean` produces an accepted witness. Combining that
proved existence statement with the lemmas below gives these consequences for
an accepted construction. The proofs do not inspect the tactic history or
require the submitted proof to follow a particular exposition.

To compile this file, follow the adjacent README. In VS Code, open the generated
review project and use Go to Definition on the identifiers in the proofs.
Compilation checks the Lean statements; the physical interpretation in these
comments remains a matter for human review.
-/
set_option autoImplicit false
noncomputable section
namespace YMReview.Chain
open YM YM.Source YM.Labels Filter Set MeasureTheory
open scoped Topology BigOperators NNReal

variable {G : Gauge}

/-!
## 1. The insertion really uses the specified local section

At fixed degree `d` and cutoff `(N,p)`, `C.localSection d` assigns a local
function of link variables to each raw coefficient vector. `places` translates
that function to the lattice site `x`. Its engineering normalization is
`a_N^(-d)`; the additional mixing is the map called `bareCoefficients` below.

This map first undoes the terminal renormalization and then applies the inverse
threshold scaling. Positivity of the threshold makes that scaling invertible.
The two linear equivalences compose to a linear equivalence on the raw label
space at this cutoff. The map can depend on both `N` and `p`.

`actual_insertion_formula` ends with `rfl`: unfolding the definitions gives
exactly the displayed local function. This checks what `C.O` denotes. It does
not prove classical matching of an arbitrary choice of local sections; that
requirement belongs to `C.Makes`, retained in `Accepted.lattice.makes`.
-/

/-- Undo the terminal renormalization and the nonzero diagonal threshold
scaling. This is an equivalence on raw coefficient space at each cutoff. -/
def bareCoefficients (C : Family G) (d N p : ℕ) :
    C.label d ≃ₗ[ℂ] C.label d :=
  let F := C.labels.level d
  let t := C.path.levels.clock.threshold N
  have ht : t ≠ 0 := (C.path.levels.budget N).threshold_pos.ne'
  let diagonal : C.label d ≃ₗ[ℂ] C.label d :=
    { F.scaled t⁻¹ with
      invFun := F.scaled t
      left_inv := F.scaled_inv ht
      right_inv := fun v => by
        have h := F.scaled_inv (inv_ne_zero ht) v
        simpa only [inv_inv] using! h }
  (C.factory d N p).terminal.symm.trans diagonal

theorem actual_insertion_formula (C : Family G) (d N p : ℕ)
    (v : C.label d) (x : Lattice.Site (C.side N p)) :
    C.O N p v x = ((C.S.a N : ℂ)^d)⁻¹ •
      (C.localSection d).places (bareCoefficients C d N p v) x := rfl

/-!
## 2. No raw coefficient direction is removed at a finite cutoff

Surjectivity of `bareCoefficients` lets us start with any coefficient vector
`c` and find the renormalized label `v` which represents it. The same `v` works
at every site of this fixed lattice. The common factor `a_N^(-d)` remains.

The following two statements concern finite cutoffs. They do not bound the
inverse coefficient map uniformly as the cutoff is removed. In particular,
they do not by themselves exclude a trivial or degenerate continuum limit.
That requires the accepted field-content and short-distance results as well.
-/

/-- Every placed primary section is represented by an actual renormalized
insertion, up to the common engineering factor. No coefficient direction is
discarded by the finite-cutoff renormalization map. -/
theorem every_primary_is_represented (C : Family G) (d N p : ℕ)
    (c : C.label d) :
    ∃ v : C.label d, ∀ x : Lattice.Site (C.side N p),
      C.O N p v x = ((C.S.a N : ℂ)^d)⁻¹ • (C.localSection d).places c x := by
  refine ⟨(bareCoefficients C d N p).symm c, fun x => ?_⟩
  rw [actual_insertion_formula, LinearEquiv.apply_symm_apply]

/-!
The next lemma has an explicit hypothesis: a primary local function takes
different values on two configurations `U` and `V`. An invertible change of
coefficients and a nonzero common scale cannot make *every* insertion constant.
It does not assert that every local section is nonconstant, or that a chosen
field has nonzero correlations after taking limits.
-/

/-- Nonconstant primary observables cannot all become constants merely by
the terminal renormalization. This is a finite-cutoff statement. -/
theorem nonconstant_primary_survives (C : Family G) (d N p : ℕ)
    (c : C.label d) (x : Lattice.Site (C.side N p))
    (U V : Wilson.Config G (C.side N p))
    (different : (C.localSection d).places c x U ≠ (C.localSection d).places c x V) :
    ∃ v : C.label d, C.O N p v x U ≠ C.O N p v x V := by
  obtain ⟨v,hv⟩ := every_primary_is_represented C d N p c
  refine ⟨v, fun same => different ?_⟩
  rw [hv x] at same
  have nz : ((C.S.a N : ℂ)^d)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne'))
  exact (mul_left_cancel₀ nz) same

variable {g : YangMills.GaugeGroup} {C : Family g.core}
variable {o : Extraction.Order} {S : Table C.book} {F : Spec.Final C o S}

/-!
## 3. Continuum field words have lattice representatives

A local field in `S.Field d` is a class in a quotient of the degree-`d` raw
labels. `S.Tag` packages its degree together with that class. For every field
in the word `a`, the proof chooses `S.representative` once. This choice depends
on `S` and `a`, not on the cutoff or volume. The associated lattice insertions
still vary with `(N,p)` through `C.O` and its renormalization maps.

The test `t` is a joint smooth, compactly supported test away from coincidence.
The smeared lattice moment is `smear N p v t`. The proof obtains a sequence
`row p` of fixed-volume continuum pairings:

  smear N p v t → row p                  as N → ∞,
  row (o.per k) → ∫ x, t x * S.useAt S x a  as k → ∞.

The first limit is asserted for volumes `suitable` for the test's support.
The second is a subsequential volume limit. The theorem does not assert
interchange of the limits, a rate, or uniqueness across volume subsequences.

Most importantly, its right-hand side uses the *mixed table* `S`. Replacing
that table by a selected phase is not justified by this lemma. Phase selection
is the next part of the construction.
-/

/-- Quotient fields have fixed raw representatives, and their entire mean
correlation functions are limits of those representatives' lattice moments. -/
theorem every_field_word_has_lattice_origin (hg : g.IsSimple)
    (h : Acceptance.Accepted hg F) (n : ℕ) (a : Fin n → S.Tag)
    (t : YangMills.WilsonFamily.SeparatedTest n) :
    ∃ v : Fin n → C.book.Token, (∀ i, S.classTokens (v i) = a i) ∧
      ∃ row : ℕ → ℂ,
        (∀ p, (YangMills.wilsonFamily C).suitable p t →
          Tendsto (fun N => (YangMills.wilsonFamily C).smear N p v t) atTop (𝓝 (row p))) ∧
        Tendsto (fun k => row (o.per k)) atTop
          (𝓝 (∫ x, t x * S.useAt S x a)) := by
  let v : Fin n → C.book.Token := fun i => ⟨(a i).1,S.representative _ (a i).2⟩
  have hv : S.classTokens ∘ v = a := by
    funext i
    simp only [Function.comp_apply,v,Table.classTokens,S.rep]
  obtain ⟨_,row,hrow,hlimit⟩ := h.lattice.public_limit n v t
  refine ⟨v,fun i => congrFun hv i,row,hrow,?_⟩
  convert hlimit using 2
  congr 1

/-!
## 4. Phase readings come from the actual ground-state algebra

The OS reconstruction of the mixed hierarchy gives a Hilbert space and a
zero-energy subspace. A distinct local word, translated into a suitable
positive-time slab, defines a bounded insertion operator. Compressing it to
the zero-energy subspace gives the operator represented here by `slot`.
These operators belong to the commutative ground-state algebra in `F`.

The phase certificate identifies the expectation of an entire word with a
character evaluated on its slot. Its representing measure integrates algebra
elements to their vacuum expectation in the same ground-state representation.

Apply that representation to the *product* of two slots. Multiplicativity of
characters (`map_mul`) gives the next equation. This constraint contains more
information than the barycenter identity alone: products of phase readings
are tied to products in the actual algebra. It is not a factorization of a
phase's multipoint correlation into single-field expectations. Each slot here
already represents a whole word.

This does not say that each phase is itself a volume subsequential limit of
the original periodic lattice states, nor that there is only one phase.
-/

/-- The phase certificate fixes products of phase readings through products
of the actual compressed operators. It is stronger than a barycenter alone. -/
theorem phase_second_moments_are_ground_products
    (w u : C.book.Word) (hw : Word.distinct w) (hu : Word.distinct u)
    (s t : E4) (d e : ℝ≥0)
    (hs : OS.Slab timeAxis d (Word.carry w s))
    (ht : OS.Slab timeAxis e (Word.carry u t)) :
    (∫ i, (F.α.ensemble i).expect w * (F.α.ensemble i).expect u ∂F.α.space.μ) =
      inner ℂ F.α.room.omega0
        ((F.α.unselected.slot _ _ hs * F.α.unselected.slot _ _ ht).val F.α.room.omega0) := by
  have h := F.phase.phase.decomposition.ground
    (F.α.unselected.slot _ _ hs * F.α.unselected.slot _ _ ht)
  simp only [map_mul] at h
  simpa only [F.phase.phase.chosen _ w hw s d hs,
    F.phase.phase.chosen _ u hu t e ht] using h

/-!
## 5. Reconstruction uses the selected phase's boundary distribution

A `Boundary.Sentence S` is a finite field word with its smearing tests. The
reconstructed field product applied to the vacuum is `operators.vector w`.
Its vacuum expectation is identified with `F.A.world.expect w` by the
realization certificate `qt.meets` belonging to the same `F`.

The rest of `Spec.Final` identifies this contour with the continuation of the
selected phase. The one-line proof below exposes the expectation identity;
it is not a new proof of analytic continuation or OS reconstruction.
-/

/-- The selected relativistic field words are tied to the boundary values of
the selected phase's continuation, rather than to another QFT. -/
theorem reconstructed_words_are_selected_boundary (w : Boundary.Sentence S) :
    inner ℂ F.action.operators.vacuum (F.action.operators.vector w) = F.A.world.expect w :=
  F.realization.qt.meets w

/-!
## 6. A fixed analytic continuation has a unique boundary value

Suppose two candidate contours come from the same selected phase and have
*equal analytic continuations*, the hypothesis `same : A.waves = B.waves`.
Their distributional boundary limits, tested against the same joint test,
must agree by uniqueness of limits in the complex numbers.

The profile parameter approaches the boundary inside the allowed domain;
`y` and `hy` specify an admissible approach direction. The conclusion concerns
the distributional pairing `world.W n v f`, not a pointwise value at a singular
configuration. The test `f : Boundary.Joint n` is a joint Schwartz test.

Do not drop the `same` hypothesis: this lemma does not establish uniqueness of
analytic continuation from Euclidean data, uniqueness of an IR subsequential
limit, or uniqueness of the phase. Those are different assertions.
-/

/-- The boundary distribution cannot be independently changed while keeping
the same continuation: limits against every joint test are unique. -/
theorem same_continuation_same_boundary (A B : Boundary.Contour S)
    (hA : A.From (F.α.ensemble F.α.atPoint))
    (hB : B.From (F.α.ensemble F.α.atPoint))
    (same : A.waves = B.waves) (n : ℕ) (v : Fin n → S.Union)
    (y : Boundary.Heights n) (hy : y ∈ Boundary.east n) (f : Boundary.Joint n) :
    A.world.W n v f = B.world.W n v f := by
  have ha := hA.emerges.profile n v y hy f
  have hb := hB.emerges.profile n v y hy f
  rw [same] at ha
  exact tendsto_nhds_unique ha hb

end YMReview.Chain

/-!
## Reading the axiom report

These commands expose the transitive axiom dependencies of the seven lemmas.
The permitted logical foundations in the review are `propext`,
`Classical.choice`, and `Quot.sound`. A successful ordinary Lean compilation
and these reports are supplementary evidence. They do not constitute another
Comparator run or a fresh rebuild of all imported dependencies.
-/

#print axioms YMReview.Chain.actual_insertion_formula
#print axioms YMReview.Chain.every_primary_is_represented
#print axioms YMReview.Chain.nonconstant_primary_survives
#print axioms YMReview.Chain.every_field_word_has_lattice_origin
#print axioms YMReview.Chain.phase_second_moments_are_ground_products
#print axioms YMReview.Chain.reconstructed_words_are_selected_boundary
#print axioms YMReview.Chain.same_continuation_same_boundary
