import YangMills.Renormalization
import YangMills.CompositeExtraction

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
Checks of the imported finite-cutoff coefficient engine. These are identities
of its actual kernels, including their color and derivative conventions.
They do not identify bare coefficients with generated renormalized OPE data.
-/
noncomputable section
open scoped BigOperators
namespace YMYMG.KernelAudit
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow

variable {G : CompactSimpleGaugeGroup}

theorem wick_four_bosons (s : CutoffScales) (a b c d : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    wickKernel s [a,b,c,d] =
      contraction s a b * contraction s c d +
      contraction s a c * contraction s b d +
      contraction s a d * contraction s b c := by
  simp [wickKernel, wickCrossingSign, ha, Fin.sum_univ_succ]
  ring

theorem wick_four_fermions (s : CutoffScales) (a b c d : PositionedLeg G)
    (ha : a.field.fermionic = true) (hb : b.field.fermionic = true)
    (hc : c.field.fermionic = true) :
    wickKernel s [a,b,c,d] =
      contraction s a b * contraction s c d -
      contraction s a c * contraction s b d +
      contraction s a d * contraction s b c := by
  simp [wickKernel, wickCrossingSign, ha, hb, hc, Fin.sum_univ_succ]
  ring

theorem wick_four_equal (s : CutoffScales) (a : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    wickKernel s [a,a,a,a] = 3 * contraction s a a ^ 2 := by
  rw [wick_four_bosons s a a a a ha]
  ring

theorem wick_six_equal (s : CutoffScales) (a : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    wickKernel s [a,a,a,a,a,a] = 15 * contraction s a a ^ 3 := by
  rw [wickKernel]
  simp [Fin.sum_univ_succ, wickCrossingSign, ha, wick_four_equal s a ha]
  ring

/-- Actual vacuum-normalized bare coefficient, with its required analytic
side conditions retained. The order is zero in the canonical coupling. -/
theorem bare_four_equal {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (finite : BareCoefficientIntegrability s e switching) (a : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    bareCoefficient s e switching finite [a,a,a,a] 0 =
      3 * contraction s a a ^ 2 := by
  exact (bareNormalizedCoefficient_zero s e switching _).trans
    (wick_four_equal s a ha)

theorem bare_six_equal {B : InvariantForm G} (s : CutoffScales)
    (e : ColorFrame B) (switching : SchwartzMap Spacetime ℝ)
    (finite : BareCoefficientIntegrability s e switching) (a : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    bareCoefficient s e switching finite [a,a,a,a,a,a] 0 =
      15 * contraction s a a ^ 3 := by
  exact (bareNormalizedCoefficient_zero s e switching _).trans
    (wick_six_equal s a ha)

/-- The standard Gaussian subtraction cancels the actual native vacuum
contractions. This is a finite-cutoff algebra identity, not a renormalized
physical insertion or a proof of the generated CS equation. -/
theorem wick_normal_four_vacuum (s : CutoffScales) (a : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    wickKernel s [a,a,a,a] - 6 * contraction s a a * wickKernel s [a,a] +
      3 * contraction s a a ^ 2 * wickKernel (G := G) s [] = 0 := by
  rw [wick_four_equal s a ha, wickKernel_pair, wickKernel_nil]
  ring

theorem wick_normal_four_two_legs (s : CutoffScales) (a : PositionedLeg G)
    (ha : a.field.fermionic = false) :
    wickKernel s [a,a,a,a,a,a] - 6 * contraction s a a * wickKernel s [a,a,a,a] +
      3 * contraction s a a ^ 2 * wickKernel s [a,a] = 0 := by
  rw [wick_six_equal s a ha, wick_four_equal s a ha, wickKernel_pair]
  ring

def normalTwo (v x : ℂ) : ℂ := x ^ 2 - v
def normalFour (v x : ℂ) : ℂ := x ^ 4 - 6*v*x^2 + 3*v^2

/-- A change of Gaussian subtraction produces an exact lower-degree
coefficient. It need not vanish just because both prescriptions are normal
ordered. Its identification with physical YM mixing is a separate problem. -/
theorem normal_four_change (v w x : ℂ) :
    normalFour v x = normalFour w x + 6*(w-v)*normalTwo w x + 3*(w-v)^2 := by
  unfold normalFour normalTwo
  ring

def derivativeLeg (mu nu : Fin 4) (a : Fin G.dimension) (x : Spacetime) :
    PositionedLeg G := ⟨⟨.gauge nu a, [mu]⟩, x⟩

/-- The free F_01 = partial_0 A_1 - partial_1 A_0 component, retaining
all four terms before the native diagonal covariance eliminates two. -/
def curvature01Integrand (s : CutoffScales) (a b : Fin G.dimension)
    (x p : Spacetime) : ℂ :=
  contractionIntegrand s (derivativeLeg 0 1 a x) (derivativeLeg 0 1 b x) p -
  contractionIntegrand s (derivativeLeg 0 1 a x) (derivativeLeg 1 0 b x) p -
  contractionIntegrand s (derivativeLeg 1 0 a x) (derivativeLeg 0 1 b x) p +
  contractionIntegrand s (derivativeLeg 1 0 a x) (derivativeLeg 1 0 b x) p

theorem curvature01_integrand (s : CutoffScales) (a b : Fin G.dimension)
    (x p : Spacetime) :
    curvature01Integrand s a b x p =
      if a = b then (((p 0)^2 + (p 1)^2 : ℝ) : ℂ) *
        (flowCovariance s p : ℂ) / (2 * Real.pi : ℂ)^4 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [curvature01Integrand, derivativeLeg, contractionIntegrand,
      basicCovariance, euclideanPair]
    ring_nf
  · simp [curvature01Integrand, derivativeLeg, contractionIntegrand,
      basicCovariance, hab, euclideanPair]

/-- Renormalized boundary coefficients cannot simply be replaced by the
bare Wick contractions: the actual insertion normalization fixes these
lower coefficients to zero at the subtraction point. -/
theorem normalized_lower_output_zero
    {L : InsertedFlowFamily G} {mu : ℝ}
    (h : SingleInsertionBoundaryConditions L mu)
    (A B : LocalMonomial G) (hA : A.Admissible) (hB : B.Admissible)
    (hDim : B.dimension < A.dimension) (loop : ℕ) (UV : ℝ) (hUV : mu ≤ UV) :
    extractCoefficient B (L [⟨A, 0⟩] loop mu UV) 0 = 0 := by
  rw [h.normalized A B hA hB (Nat.le_of_lt hDim) loop UV hUV]
  have hne : A ≠ B := by
    intro he
    subst B
    exact (lt_irrefl _ hDim)
  simp [hne]

#print axioms wick_four_bosons
#print axioms wick_four_fermions
#print axioms wick_four_equal
#print axioms wick_six_equal
#print axioms bare_four_equal
#print axioms bare_six_equal
#print axioms wick_normal_four_vacuum
#print axioms wick_normal_four_two_legs
#print axioms normal_four_change
#print axioms curvature01_integrand
#print axioms normalized_lower_output_zero

end YMYMG.KernelAudit
