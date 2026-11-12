import YangMills.FilteredQuantumRG
import YangMills.FlowScaleConstancy
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
The renormalized Gaussian curvature channel, including its subtraction
counterterms and changes of prescription. Color multiplicity is arbitrary.
This computes a leading free contraction sector; identifying it with an
entire generated physical YM prescription remains a separate obligation.
-/
noncomputable section
open scoped BigOperators
namespace YMYMG.RenormalizedGaussian
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow

def colorSquare (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∑ a : Fin n, MvPolynomial.X a ^ 2

def halfLaplacian {n : ℕ} (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  (1/2 : ℂ) • ∑ a : Fin n, MvPolynomial.pderiv a (MvPolynomial.pderiv a P)

theorem colorSquare_derivative (n : ℕ) (a : Fin n) :
    MvPolynomial.pderiv a (colorSquare n) = 2 * MvPolynomial.X a := by
  classical
  simp [colorSquare, map_sum, MvPolynomial.pderiv_X, Pi.single_apply]

private theorem pderiv_two {n : ℕ} (a : Fin n) :
    MvPolynomial.pderiv a (2 : MvPolynomial (Fin n) ℂ) = 0 :=
  (MvPolynomial.pderiv a).map_natCast 2

theorem halfLaplacian_square (n : ℕ) :
    halfLaplacian (colorSquare n) = MvPolynomial.C (n : ℂ) := by
  classical
  have hs : (∑ a : Fin n, MvPolynomial.pderiv a
      (MvPolynomial.pderiv a (colorSquare n))) = (2 : ℂ) • MvPolynomial.C (n : ℂ) := by
    simp [colorSquare_derivative, pderiv_two,
      MvPolynomial.smul_eq_C_mul, map_ofNat, mul_comm]
  rw [halfLaplacian, hs, smul_smul]
  norm_num

theorem halfLaplacian_four (n : ℕ) :
    halfLaplacian (colorSquare n ^ 2) =
      MvPolynomial.C (2 * ((n : ℂ) + 2)) * colorSquare n := by
  classical
  have hi (a : Fin n) :
      MvPolynomial.pderiv a (MvPolynomial.pderiv a (colorSquare n ^ 2)) =
        4 * colorSquare n + 8 * MvPolynomial.X a ^ 2 := by
    simp [colorSquare_derivative, pderiv_two]
    ring
  simp only [halfLaplacian, hi, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  change (1/2 : ℂ) • ((n : MvPolynomial (Fin n) ℂ) * (4 * colorSquare n) +
    8 * colorSquare n) = _
  have hs : ((n : MvPolynomial (Fin n) ℂ) * (4 * colorSquare n) + 8 * colorSquare n) =
      (2 : ℂ) • (MvPolynomial.C (2 * ((n : ℂ) + 2)) * colorSquare n) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_add, map_natCast, map_ofNat]
    ring
  rw [hs, smul_smul]
  norm_num

/-- Cutoff-independent difference of the coincident free curvature variances.
The 4D Fourier integral giving this expression is recorded separately. -/
def varianceDifference (mu cutoff : ℝ) : ℝ :=
  (mu ^ 4 - cutoff ^ 4) / (32 * Real.pi ^ 2)

def quadraticShift (n : ℕ) (mu cutoff : ℝ) : ℝ :=
  (n : ℝ) * varianceDifference mu cutoff

def quarticShift (n : ℕ) (mu cutoff : ℝ) : ℝ :=
  2 * ((n : ℝ) + 2) * varianceDifference mu cutoff

theorem subtraction_boundary (n : ℕ) (mu : ℝ) :
    quadraticShift n mu mu = 0 ∧ quarticShift n mu mu = 0 := by
  simp [quadraticShift, quarticShift, varianceDifference]

theorem quarticShift_flow (n : ℕ) (mu cutoff : ℝ) :
    HasDerivAt (quarticShift n mu)
      (-(n + 2 : ℝ) * cutoff ^ 3 / (4 * Real.pi ^ 2)) cutoff := by
  have hd := (((hasDerivAt_id cutoff).pow 4).const_sub (mu^4)).div_const
    (32 * Real.pi^2)
  convert hd.const_mul (2 * ((n : ℝ) + 2)) using 1 <;> try rfl
  dsimp only [id_eq]
  ring

theorem quarticShift_ir (n : ℕ) (mu : ℝ) :
    quarticShift n mu 0 = ((n : ℝ) + 2) * mu ^ 4 / (16 * Real.pi ^ 2) := by
  simp [quarticShift, varianceDifference]
  ring

/-- Subtracting at mu removes the UV cutoff exactly. Both covariances
are the expressions evaluated by CurvatureVariance.native_curvature_variance. -/
theorem variance_subtraction (mu cutoff UV : ℝ) :
    (UV^4 - cutoff^4) / (32 * Real.pi^2) -
      (UV^4 - mu^4) / (32 * Real.pi^2) = varianceDifference mu cutoff := by
  unfold varianceDifference
  ring

/-- Once a channel's actual flow is reduced to this Gaussian right-hand
side, its normalized solution is forced, including the UV endpoint.
The reduction of a complete YM insertion flow to this ODE is a hypothesis. -/
theorem quarticShift_unique (n : ℕ) (mu UV : ℝ) (f : ℝ → ℂ)
    (hmu : 0 < mu) (hmuUV : mu ≤ UV)
    (hc : ContinuousOn f (Set.Ioc 0 UV))
    (hf : ∀ cutoff, 0 < cutoff → cutoff < UV →
      HasDerivAt f (-(n + 2 : ℝ) * cutoff^3 / (4 * Real.pi^2) : ℝ) cutoff)
    (hb : f mu = 0) (cutoff : ℝ) (hp : 0 < cutoff) (hUV : cutoff ≤ UV) :
    f cutoff = (quarticShift n mu cutoff : ℝ) := by
  have hq : Continuous (fun cutoff => (quarticShift n mu cutoff : ℂ)) := by
    unfold quarticShift varianceDifference
    fun_prop
  have he := positiveScale_constancy (UV := UV)
    (f := fun cutoff => f cutoff - (quarticShift n mu cutoff : ℂ))
    (hc.sub hq.continuousOn)
    (fun t ht hlt => by
      simpa only [sub_self] using!
        (hf t ht hlt).sub (quarticShift_flow n mu t).ofReal_comp)
    hp hUV hmu hmuUV
  simpa only [hb, (subtraction_boundary n mu).2, Complex.ofReal_zero, sub_zero,
    sub_eq_zero] using he

/-- The CS convention is mu*d O / d mu = -gamma O. This is the
dimension-lowering coefficient of the computed Gaussian prescription. -/
def gaussianGamma (n : ℕ) (mu : ℝ) : ℝ :=
  -((n : ℝ) + 2) * mu ^ 4 / (4 * Real.pi ^ 2)

theorem subtraction_scale_derivative (n : ℕ) (mu : ℝ) :
    HasDerivAt (fun scale => quarticShift n scale 0)
      (((n : ℝ) + 2) * mu ^ 3 / (4 * Real.pi ^ 2)) mu := by
  simp only [quarticShift_ir]
  convert (((hasDerivAt_id mu).pow 4).const_mul ((n : ℝ) + 2)).div_const
    (16 * Real.pi^2) using 1 <;> try rfl
  dsimp only [id_eq]
  ring

theorem gaussianGamma_nonzero (n : ℕ) (mu : ℝ) (hmu : 0 < mu) :
    gaussianGamma n mu ≠ 0 := by
  unfold gaussianGamma
  have hn : (0 : ℝ) < n + 2 := by positivity
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hn))
    (pow_ne_zero 4 (ne_of_gt hmu))) (by positivity)

/-- A finite lower-degree quantum correction cancels this particular
one-loop scale dependence. No full corrected-YM family is asserted here. -/
def cancellingCorrection (n : ℕ) (mu : ℝ) : ℝ := -quarticShift n mu 0

theorem corrected_lower_coefficient (n : ℕ) (mu : ℝ) :
    quarticShift n mu 0 + cancellingCorrection n mu = 0 := by
  simp [cancellingCorrection]

theorem corrected_gamma (n : ℕ) (mu : ℝ) :
    gaussianGamma n mu - mu * deriv (cancellingCorrection n) mu = 0 := by
  have hd := (subtraction_scale_derivative n mu).neg
  change HasDerivAt (cancellingCorrection n) _ mu at hd
  rw [hd.deriv]
  unfold gaussianGamma
  ring

/-- At one loop, a four-field insertion and two external fields leave
no interaction vertices. A higher-field term also cannot contribute. -/
theorem one_loop_graph_count (insertionLegs cubic quartic edges : ℕ)
    (hmin : 4 ≤ insertionLegs)
    (hhalf : insertionLegs + 3*cubic + 4*quartic = 2 + 2*edges)
    (hloop : edges = 1 + cubic + quartic) :
    insertionLegs = 4 ∧ cubic = 0 ∧ quartic = 0 := by omega

#print axioms colorSquare_derivative
#print axioms halfLaplacian_square
#print axioms halfLaplacian_four
#print axioms subtraction_boundary
#print axioms quarticShift_flow
#print axioms quarticShift_ir
#print axioms variance_subtraction
#print axioms quarticShift_unique
#print axioms subtraction_scale_derivative
#print axioms gaussianGamma_nonzero
#print axioms corrected_lower_coefficient
#print axioms corrected_gamma
#print axioms one_loop_graph_count
end YMYMG.RenormalizedGaussian
