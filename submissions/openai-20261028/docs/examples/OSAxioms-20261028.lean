import CombinedAcceptance

/-!
# [A1] The independent OS comparison — 28 October 2026

This example follows the scalar hierarchy used in the comparison with the
Douglas–Mei–Yin OS axioms. It explains existing bridge proofs; it does not
replace their definitions or add an acceptance requirement.

`F : Spec.Final C o S` fixes the construction data. `S` is the mixed table
obtained from lattice limits. `Trace.state F` is the selected character phase;
`Trace.traceField F` is the stress trace centered in that phase. These choices
are used throughout. In particular, the E4 result below is a statement about
the selected phase, not a claim that the mixed table clusters.

The `3` in `OsterwalderSchraderAxioms 3` counts spatial dimensions: the
Euclidean configuration space has four coordinates per insertion. This
independent bridge concerns repeated insertions of one scalar field. The
submission's reconstruction of its full field collection is a separate result.
-/

set_option autoImplicit false
noncomputable section
namespace YMReview.Examples.OSAxioms
open YM MeasureTheory YangMills.OSRecon
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-!
## 1. Which correlation functions are being tested?

`scalarKernel F n` is the selected n-point function of the centered trace.
`configEquiv` only changes coordinate representations. The bridge's real
`targetKernel` agrees with that complex-valued correlation at every separated
configuration; the source reality theorem supplies this identification.

On a coincidence diagonal `targetKernel` is defined to be zero. This makes a
measurable function on the whole configuration space. It is not a claim that
the physical distribution has no contact terms.
-/

theorem kernel_is_the_selected_correlation {n : ℕ}
    (x : NPointDomain 3 n) (hx : Function.Injective x) :
    (YMOSBridge.targetKernel F n x : ℂ) =
      YMOSBridge.scalarKernel F n (YMOSBridge.configEquiv n x) :=
  YMOSBridge.targetKernel_eq F x hx

/-!
## 2. Singularities and the test-function domain

`ZeroDiagonalSchwartz 3 n` consists of joint Schwartz tests flat to all orders
on every coincidence diagonal. It is not just a space of products of one-point
tests, nor does “zero diagonal” mean only that the function value vanishes.

The separated kernel has a finite inverse-power bound in the minimum
separation (capped at one). Flatness absorbs this singularity, and Schwartz
decay controls infinity. The bridge proves integrability before identifying
the functional with the integral. This matters because Lean's integral is
totalized: an integral expression alone would not prove integrability.
-/

theorem separated_bound (n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : NPointDomain 3 n, Function.Injective x →
        ‖YMOSBridge.targetKernel F n x‖ ≤
          B * (YMOSBridge.separation x ^ N)⁻¹ :=
  YMOSBridge.targetKernel_bound F n

theorem pairing_is_integrable (n : ℕ) (f : ZeroDiagonalSchwartz 3 n) :
    Integrable (fun x : NPointDomain 3 n =>
      (YMOSBridge.targetKernel F n x : ℂ) * f.1 x) :=
  YMOSBridge.schwinger_integrable F n f

theorem pairing_is_the_selected_integral (n : ℕ) (f : ZeroDiagonalSchwartz 3 n) :
    YMOSBridge.schwinger F n f = ∫ x : NPointDomain 3 n,
      YMOSBridge.scalarKernel F n (YMOSBridge.configEquiv n x) * f.1 x :=
  YMOSBridge.schwinger_eq_selected_integral F n f

theorem E0_continuity (n : ℕ) : Continuous (YMOSBridge.schwinger F n) :=
  YMOSBridge.E0_tempered F n

/-!
## 3. Growth as the number of fields increases

Continuity at each fixed n does not provide E0′: its constants could grow
arbitrarily with n. `YM.Work.B11.phase_cap` supplies a common bound of the form
K^n (n/r)^(A n) for the fixed field at separation r. `ArityGrowth.lean`
transports it through the diagonal-flat integral estimate and absorbs the
n^(A n) factor into an exponential times (n!)^A.

The order of quantifiers below is essential. The seminorm slope `s`, base
`β`, and factorial exponent `A` are chosen once, before n and the test f.
Both seminorm indices grow at most linearly in n. The finite supremum is the
actual Schwartz seminorm expression used in the target, not an unspecified
norm that can be chosen independently at each arity.
-/

theorem E0_prime_uniform_arity :
    ∃ s : ℕ, ∃ β : ℝ, ∃ A : ℕ, 0 < β ∧
      ∀ (n : ℕ) (f : ZeroDiagonalSchwartz 3 n),
        ‖YMOSBridge.schwinger F n f‖ ≤ β ^ n * (n.factorial : ℝ) ^ A *
          (Finset.Iic (n * s, n * s)).sup
            (schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ) f.1 :=
  YMOSBridge.E0_prime_growth F

/-!
## 4. Reflection positivity and clustering

For E2, `ReflectionPositivity.lean` first identifies the finite compact-test
reflection form entry by entry with the source positive form. Support-
preserving compact cutoffs and E0 continuity extend it to the target's full
ordered-positive-time Schwartz domain. The Borchers sequence allows mixed
arities and complex coefficients, including its vacuum component.
-/

theorem E2_full_target_form (B : BorchersSequence 3)
    (hB : ∀ n, tsupport (B.funcs n : NPointDomain 3 n → ℂ) ⊆
      OrderedPositiveTimeRegion 3 n) :
    (OSInnerProduct 3 (YMOSBridge.schwinger F) B B).re ≥ 0 :=
  YMOSBridge.E2_reflection_positive F B hB

/-!
The E4 bridge uses the phase's vacuum factorization and extends the resulting
kernel limit to the joint Schwartz pairings. The statement below displays
what “far apart” means: translate the second group by a vector whose norm
tends to infinity. The translated test and the product must belong to the
specified diagonal-flat spaces; these are hypotheses, not suppressed choices.
`CompleteOS.E4_cluster` then supplies the precise spatial-translation clause
of the independent OS record. Neither statement specifies an exponential
rate, proves a mass gap, or makes the infrared extraction unique.
-/

theorem E4_separated_groups (n m : ℕ) (f : ZeroDiagonalSchwartz 3 n)
    (g : ZeroDiagonalSchwartz 3 m) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ a : SpacetimeDim 3, R < ‖a‖ →
      ∀ g_a : ZeroDiagonalSchwartz 3 m,
        (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
        ∀ fg_a : ZeroDiagonalSchwartz 3 (n + m),
          (∀ x, fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
          ‖YMOSBridge.schwinger F (n + m) fg_a -
            YMOSBridge.schwinger F n f * YMOSBridge.schwinger F m g‖ < ε :=
  YMOSBridge.E4_cluster_norm F n m f g ε hε

/-!
## 5. The complete record and its scope

`verifiedOS` also packages E1 Euclidean invariance, E3 permutation symmetry,
normalization and the required linearity. Its S field is exactly the pairing
above. There is no second choice of theory when the growth condition is added.

Compilation checks this instance of the imported OS definition. The separate
source-correspondence audit records how those definitions match the bundled
OSreconstruction snapshot. This file does not prove or invoke the entire
Douglas–Mei–Yin reconstruction theorem. The submission has its own Wightman
reconstruction, retained elsewhere in the combined target.

Diagonal-flat tests annihilate distributions supported on coincidence
diagonals. Consequently this OS comparison does not establish uniqueness of
Euclidean contact extensions or unrestricted OS positivity for such an
extension. These are different questions from the axioms proved here.
-/

theorem complete_OS_on_this_hierarchy :
    ∃ axioms : OsterwalderSchraderAxioms 3,
      axioms.S = YMOSBridge.schwinger F ∧
      Nonempty (OSArityLinearGrowthCondition 3 axioms) :=
  ⟨YMOSBridge.verifiedOS F, rfl, YMOSBridge.verifiedOS_growth F⟩

#print axioms kernel_is_the_selected_correlation
#print axioms separated_bound
#print axioms pairing_is_integrable
#print axioms pairing_is_the_selected_integral
#print axioms E0_continuity
#print axioms E0_prime_uniform_arity
#print axioms E2_full_target_form
#print axioms E4_separated_groups
#print axioms complete_OS_on_this_hierarchy
end YMReview.Examples.OSAxioms
