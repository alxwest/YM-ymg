import YangMills.Renormalization
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace YMYMG.CurvatureVariance
open YangMills YangMills.Perturbative

theorem regulator_product (scale : ℝ) (p : Spacetime) :
    exponentialRegulator scale p =
      ∏ i : Fin 4, Real.exp (-(scale^2)⁻¹ * (p i)^2) := by
  unfold exponentialRegulator euclideanSquare
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  ring

theorem regulator_integrable (scale : ℝ) (hs : 0 < scale) :
    Integrable (exponentialRegulator scale) := by
  have h : Integrable (fun p : Spacetime =>
      ∏ i : Fin 4, Real.exp (-(scale^2)⁻¹ * (p i)^2)) :=
    Integrable.fintype_prod (fun _ : Fin 4 => integrable_exp_neg_mul_sq (by positivity))
  simpa only [← regulator_product] using h

theorem regulator_integral (scale : ℝ) (hs : 0 < scale) :
    (∫ p : Spacetime, exponentialRegulator scale p) = Real.pi^2 * scale^4 := by
  simp_rw [regulator_product]
  rw [integral_fintype_prod_volume_eq_prod
    (fun _ : Fin 4 => fun x : ℝ => Real.exp (-(scale^2)⁻¹ * x^2))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [integral_gaussian]
  have hp : 0 ≤ Real.pi / (scale^2)⁻¹ := by positivity
  rw [show (4 : ℕ) = 2*2 by rfl, pow_mul, Real.sq_sqrt hp]
  field_simp

def weight (i : Fin 4) (p : Spacetime) : ℝ :=
  if euclideanSquare p = 0 then 1/4 else (p i)^2 / euclideanSquare p

theorem weight_bounds (i : Fin 4) (p : Spacetime) :
    0 ≤ weight i p ∧ weight i p ≤ 1 := by
  have hq := euclideanSquare_nonnegative p
  have hi : (p i)^2 ≤ euclideanSquare p :=
    Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  unfold weight
  split_ifs with hz
  · norm_num
  · constructor
    · positivity
    · exact (div_le_one (lt_of_le_of_ne hq (Ne.symm hz))).mpr hi

theorem weight_sum (p : Spacetime) : (∑ i : Fin 4, weight i p) = 1 := by
  unfold weight
  split_ifs with hz
  · norm_num
  · rw [← Finset.sum_div]
    exact div_self hz

theorem covariance_weight (s : CutoffScales) (i : Fin 4) (p : Spacetime) :
    (p i)^2 * flowCovariance s p =
      weight i p * (exponentialRegulator s.ultraviolet p -
        exponentialRegulator s.infrared p) := by
  have hi : (p i)^2 ≤ euclideanSquare p :=
    Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  unfold flowCovariance weight
  split_ifs with hz
  · have hsq : (p i)^2 = 0 := le_antisymm (by simpa [hz] using hi) (sq_nonneg _)
    simp [hsq, exponentialRegulator, hz]
  · ring

def weighted (s : CutoffScales) (i : Fin 4) (p : Spacetime) : ℝ :=
  weight i p * (exponentialRegulator s.ultraviolet p - exponentialRegulator s.infrared p)

theorem weighted_integrable (s : CutoffScales) (i : Fin 4) : Integrable (weighted s i) := by
  have hm : Measurable (weight i) := by
    unfold weight euclideanSquare
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · fun_prop
    · fun_prop
  apply ((regulator_integrable s.ultraviolet (s.infrared_pos.trans_le s.ordered)).sub
    (regulator_integrable s.infrared s.infrared_pos)).bdd_mul hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (weight_bounds i p).1] using
      (weight_bounds i p).2)

theorem square_permutation (sigma : Equiv.Perm (Fin 4)) (p : Spacetime) :
    euclideanSquare (fun i => p (sigma i)) = euclideanSquare p := by
  exact Equiv.sum_comp sigma (fun i => (p i)^2)

theorem weighted_integral_eq (s : CutoffScales) (i j : Fin 4) :
    (∫ p : Spacetime, weighted s i p) = ∫ p : Spacetime, weighted s j p := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
    (Equiv.swap i j)).integral_comp' (weighted s i)
  have he (p : Spacetime) :
      weighted s i ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (Equiv.swap i j)) p) =
        weighted s j p := by
    have hp : (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (Equiv.swap i j)) p =
        (fun k => p (Equiv.swap i j k)) := by
      funext k
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hp]
    simp only [weighted, weight, exponentialRegulator, square_permutation, Equiv.swap_apply_left]
  simpa only [he] using h.symm

theorem weighted_integral (s : CutoffScales) (i : Fin 4) :
    (∫ p : Spacetime, weighted s i p) =
      Real.pi^2 * (s.ultraviolet^4 - s.infrared^4) / 4 := by
  have hsum : (∑ j : Fin 4, ∫ p : Spacetime, weighted s j p) =
      Real.pi^2 * (s.ultraviolet^4 - s.infrared^4) := by
    rw [← integral_finsetSum _ (fun j _ => weighted_integrable s j)]
    simp only [weighted, ← Finset.sum_mul, weight_sum, one_mul]
    rw [integral_sub (regulator_integrable s.ultraviolet (s.infrared_pos.trans_le s.ordered))
      (regulator_integrable s.infrared s.infrared_pos),
      regulator_integral s.ultraviolet (s.infrared_pos.trans_le s.ordered),
      regulator_integral s.infrared s.infrared_pos]
    ring
  simp_rw [weighted_integral_eq s _ i] at hsum
  norm_num at hsum
  linarith

/-- Exact four-dimensional integral of the native real F_01 covariance
kernel. No spherical-coordinate formula or numerical quadrature is assumed. -/
theorem curvature_variance (s : CutoffScales) :
    (∫ p : Spacetime, ((p 0)^2 + (p 1)^2) * flowCovariance s p / (2*Real.pi)^4) =
      (s.ultraviolet^4 - s.infrared^4) / (32*Real.pi^2) := by
  simp_rw [add_mul, covariance_weight]
  change (∫ p : Spacetime, (weighted s 0 p + weighted s 1 p) / (2*Real.pi)^4) = _
  rw [integral_div, integral_add (weighted_integrable s 0) (weighted_integrable s 1),
    weighted_integral, weighted_integral]
  field_simp
  ring

variable {G : CompactSimpleGaugeGroup}

def derivativeLeg (mu nu : Fin 4) (a : Fin G.dimension) (x : Spacetime) :
    PositionedLeg G := ⟨⟨.gauge nu a, [mu]⟩, x⟩

/-- The actual four native contraction integrands for the linearized F_01
component. The color factor, Fourier normalization and derivative signs
are evaluated rather than assumed. -/
def curvatureIntegrand (s : CutoffScales) (a b : Fin G.dimension)
    (x p : Spacetime) : ℂ :=
  contractionIntegrand s (derivativeLeg 0 1 a x) (derivativeLeg 0 1 b x) p -
  contractionIntegrand s (derivativeLeg 0 1 a x) (derivativeLeg 1 0 b x) p -
  contractionIntegrand s (derivativeLeg 1 0 a x) (derivativeLeg 0 1 b x) p +
  contractionIntegrand s (derivativeLeg 1 0 a x) (derivativeLeg 1 0 b x) p

theorem curvature_integrand (s : CutoffScales) (a b : Fin G.dimension)
    (x p : Spacetime) :
    curvatureIntegrand s a b x p =
      if a = b then (((p 0)^2 + (p 1)^2) * flowCovariance s p /
        (2 * Real.pi)^4 : ℝ) else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [curvatureIntegrand, derivativeLeg, contractionIntegrand,
      basicCovariance, euclideanPair]
    ring_nf
  · simp [curvatureIntegrand, derivativeLeg, contractionIntegrand,
      basicCovariance, hab, euclideanPair]

theorem curvature_integrable (s : CutoffScales) (a b : Fin G.dimension)
    (x : Spacetime) : Integrable (curvatureIntegrand s a b x) := by
  classical
  change Integrable (fun p => curvatureIntegrand s a b x p)
  simp_rw [curvature_integrand]
  by_cases hab : a = b
  · simp only [hab, if_true]
    have h : Integrable (fun p : Spacetime =>
        ((p 0)^2 + (p 1)^2) * flowCovariance s p / (2 * Real.pi)^4) := by
      simp_rw [add_mul, covariance_weight]
      exact ((weighted_integrable s 0).add (weighted_integrable s 1)).div_const _
    exact h.ofReal
  · simp only [hab, if_false]
    exact integrable_zero _ _ _

/-- Exact integral of the imported complex free-contraction kernel.
This is finite-cutoff Gaussian data, not an identification with the full
renormalized YM mixing coefficient. -/
theorem native_curvature_variance (s : CutoffScales) (a b : Fin G.dimension)
    (x : Spacetime) :
    (∫ p : Spacetime, curvatureIntegrand s a b x p) =
      if a = b then ((s.ultraviolet^4 - s.infrared^4) /
        (32 * Real.pi^2) : ℝ) else 0 := by
  classical
  simp_rw [curvature_integrand]
  by_cases hab : a = b
  · simp only [hab, if_true, integral_complex_ofReal, curvature_variance]
  · simp [hab]

#print axioms regulator_product
#print axioms regulator_integrable
#print axioms regulator_integral
#print axioms weight_bounds
#print axioms weight_sum
#print axioms covariance_weight
#print axioms weighted_integrable
#print axioms square_permutation
#print axioms weighted_integral_eq
#print axioms weighted_integral
#print axioms curvature_variance
#print axioms curvature_integrand
#print axioms curvature_integrable
#print axioms native_curvature_variance
end YMYMG.CurvatureVariance
