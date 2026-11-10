-- SPDX-License-Identifier: Apache-2.0
import CombinedAcceptance

/-!
# [A3, A5] The finite lattice law and common scale — 28 October 2026

This walkthrough connects the submitted Wilson family to the bundled `lgt`
interface and explains what the common-scale and positive-probe checks prove.
It complements `OctoberChain.lean`, which follows the renormalized insertions
through the limits and phase construction.

There are two discrete parameters: N is the ultraviolet refinement level;
p indexes physical torus sizes. The number of lattice sites on a side is
`C.side N p`, so it depends on both. The physical length is `C.S.period p`.
These quantities must not be confused when interpreting the infrared limit.
-/

set_option autoImplicit false
noncomputable section
namespace YMReview.Examples.LatticeAndScale
open YM MeasureTheory
open scoped Topology BigOperators

/-!
## 1. Same link configurations and same plaquettes

Both descriptions use group-valued link variables on a periodic four-
dimensional lattice. `configEquiv` is a measurable reindexing of those
variables. It neither fixes a gauge nor averages configurations. The
plaquette theorem checks the ordered product of four links, including the
inverses and periodic shifts. This is a check of the actual finite lattice
objects, before any limiting or reconstruction argument.
-/

theorem same_plaquette (g : YangMills.GaugeGroup) (l : ℕ+)
    (U : GaugeConnection g.image 4 l.val) (p : LatticePlaquette 4 l.val) :
    plaquetteHolonomy U p =
      YangMills.plaquette (YMLGTBridge.configEquiv g l U) p.site p.dir1 p.dir2 :=
  YMLGTBridge.plaquette_eq g l U p

/-!
## 2. Trace normalization changes the coupling convention

Put D = g.n + 1, the dimension of the chosen matrix representation (not the
Lie algebra dimension or the rank of the group). The submitted energy sums
`1 - Re Tr(U_p)/D`; the compared `lgt` action sums `β_lgt (D - Re Tr(U_p))`.
Consequently `β_submission = D β_lgt`.

Equality of the actions alone is not yet equality of normalized expectation
values. `LGTWilsonBridge` also identifies product Haar measure, the
Boltzmann density and the partition function. `MeasurePreserving` below
states equality of the resulting probability laws under `configEquiv`.
-/

theorem coupling_conversion (g : YangMills.GaugeGroup) (l : ℕ+)
    (β : ℝ) (U : GaugeConnection g.image 4 l.val) :
    wilsonAction g.image (g.n + 1) 4 l.val β U Finset.univ =
      (β * (g.n + 1 : ℕ)) * YangMills.wilsonEnergy (YMLGTBridge.configEquiv g l U) :=
  YMLGTBridge.action_eq g l β U

variable {g : YangMills.GaugeGroup} (C : Family g.core)

theorem normalized_law_on_each_lattice (N p : ℕ) :
    MeasurePreserving (YMLGTBridge.configEquiv g (C.side N p))
      (ymMeasure g.image (g.n + 1) 4 (C.side N p).val
        (C.beta N p / (g.n + 1 : ℕ)) Finset.univ)
      (YangMills.wilsonLaw g (C.side N p) (C.beta N p) g.core.probHaar) :=
  Acceptance.finite_law_on_family C N p

theorem finite_moments_are_the_family_moments (N p : ℕ) {n : ℕ}
    (v : Fin n → C.book.Token) (x : Fin n → Lattice.Site (C.side N p)) :
    (YangMills.wilsonFamily C).finiteMoment N p v x = C.numeric N p v x :=
  YangMills.moment_eq C N p v x

/-!
## 3. A common physical ruler and RG normalization

The spacing at the reference level is one in the chosen units. At every
cutoff the lattice spacing times the number of sites is the physical torus
length. `C.Makes` is the source's construction predicate, supplied by a
`Spec.Final` as `F.room.cutoff`.

The positive reference coupling below is reached at RG level zero in every
volume and cutoff. It is `C.path.β N p 0`, not the bare Wilson coefficient
`C.beta N p` used above. The latter is allowed to run with the cutoff.
Shared kinetic paths and the common insertion readout strengthen the claim
beyond simply assigning the same numerical length unit to unrelated theories.
-/

theorem reference_unit : C.S.a 0 = 1 := CommonScale.reference_spacing C

theorem side_length_in_physical_units (N p : ℕ) :
    C.S.a N * (C.side N p).val = (C.S.period p).val :=
  CommonScale.physical_side C N p

theorem one_positive_reference_coupling (h : C.Makes) :
    ∃ betaRef : ℝ, 0 < betaRef ∧ ∀ N p, C.path.β N p 0 = betaRef :=
  CommonScale.positive_common_reference C h

theorem kinetic_path_agrees_across_volumes (h : C.Makes)
    (N p q m : ℕ) (hm : m ≤ N) :
    (C.path.rep N p m).path = (C.path.rep N q m).path :=
  CommonScale.shared_kinetic_paths C h N p q m hm

theorem insertion_has_the_prescribed_reference_value (h : C.Makes)
    (d N p : ℕ) (hN : C.ref d ≤ N) (v : C.label d) :
    ((C.factory d N p).entries (C.ref d)
      ((C.factory d N p).terminal.symm v)).x = v :=
  CommonScale.reference_insertion C h d N p hN v

variable {C} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-!
## 4. A nonzero continuum probe must connect to the mixed lattice limit

The leading trace law proves a positive two-point value in the selected
phase at some small separation. The actual lattice limit is the mixed table
S. A positive value in one phase would not alone make its average positive:
that phase could have measure zero, or other values could cancel it.

`TwoPointPhysicalObservable.lean` closes this step. Reflection positivity
makes the relevant two-point value nonnegative in every character phase;
the field is held fixed as `center F`, without recentering in each phase.
Continuity in the character and full support of the phase measure turn
strict positivity at the selected point into a strictly positive average.
The barycenter identity identifies this average with the mixed correlator.
-/

theorem selected_positivity_reaches_the_lattice_limit {r : ℝ} (hr : 0 < r)
    (hp : 0 < (TraceExtension.euclidean F r).re) :
    0 < (Trace.frontCount S r (TraceExtension.center F)).re :=
  TwoPointScale.unselected_positive_of_selected F hr hp

/-!
## 5. Precisely which mass-like quantity converges?

A fixed separated two-point test t detects the nonzero mixed kernel. The
observable is the eighth root of the absolute value of its smeared lattice
correlation. The engineering grades are four plus four; a mass-dimension
interpretation also uses the convention that t is a joint smearing density.

The statement keeps t and its positive limiting value M fixed while N and p
vary. `Sequence.full` gives the full ultraviolet sequence at each suitable
volume; `o.per` is the same already selected infrared subsequence. No new
extraction is introduced for this probe. The test and its normalization can
depend on F, so this is not a canonical, phase-independent intrinsic scale.
It is also not a spectral mass, a mass gap, or a convergence rate.
-/

theorem positive_probe_on_the_accepted_witness (hg : g.IsSimple)
    (h : Acceptance.Accepted hg F) :
    ∃ (t : Test 2) (M : ℝ), 0 < M ∧
      (Extraction.Order.mk Extraction.Sequence.full o.per).limits
        (fun p => Extraction.suitable C.S p t)
        (fun N p => NonzeroScale.massMagnitude 8
          (Extraction.Order.smears C N p (Trace.unlabel (TraceExtension.center F)) t)) M :=
  h.positive_lattice_probe

/-!
The preceding calibration and fixed-probe results are complementary. The
first controls how the family is normalized across volumes; the second
rules out a zero limit for this particular correlation-derived quantity.
Neither asserts that all possible infrared extractions yield the same
theory or the same intrinsic mass. The precise limit clauses are displayed
in `OctoberChain.lean` and retained in `AcceptanceSpec.LatticeAndScale`.
-/

#print axioms same_plaquette
#print axioms coupling_conversion
#print axioms normalized_law_on_each_lattice
#print axioms finite_moments_are_the_family_moments
#print axioms reference_unit
#print axioms side_length_in_physical_units
#print axioms one_positive_reference_coupling
#print axioms kinetic_path_agrees_across_volumes
#print axioms insertion_has_the_prescribed_reference_value
#print axioms selected_positivity_reaches_the_lattice_limit
#print axioms positive_probe_on_the_accepted_witness
end YMReview.Examples.LatticeAndScale
