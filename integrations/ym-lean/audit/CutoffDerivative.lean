import YangMills.Renormalization

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace YMYMG.KernelAudit
open YangMills YangMills.Perturbative

/-- A raw scale function is needed to take a derivative without varying
proof fields of CutoffScales. It is exactly the imported covariance on
admissible scales, including the zero-momentum branch. -/
def covarianceAt (UV : ℝ) (p : Spacetime) (IR : ℝ) : ℝ :=
  if euclideanSquare p = 0 then IR⁻¹^2 - UV⁻¹^2
  else (exponentialRegulator UV p - exponentialRegulator IR p) / euclideanSquare p

theorem covarianceAt_eq (s : CutoffScales) (p : Spacetime) :
    covarianceAt s.ultraviolet p s.infrared = flowCovariance s p := rfl

theorem covariance_derivative (UV : ℝ) (p : Spacetime) (IR : ℝ) (hIR : 0 < IR) :
    HasDerivAt (covarianceAt UV p) (flowDerivativeKernel IR p) IR := by
  have hn : IR ≠ 0 := ne_of_gt hIR
  unfold covarianceAt
  split_ifs with hp
  · convert (((hasDerivAt_id IR).inv hn).pow 2).sub_const (UV⁻¹^2) using 1 <;> try rfl
    simp [flowDerivativeKernel, exponentialRegulator, hp]
    field_simp
  ·
    have hd := (((hasDerivAt_const IR (-euclideanSquare p)).div
      ((hasDerivAt_id IR).pow 2) (pow_ne_zero 2 hn)).exp)
    convert (hd.const_sub (exponentialRegulator UV p)).div_const
      (euclideanSquare p) using 1 <;> try rfl
    dsimp only [Pi.pow_apply, Pi.div_apply, id_eq]
    unfold flowDerivativeKernel exponentialRegulator
    field_simp
    ring

#print axioms covarianceAt_eq
#print axioms covariance_derivative
end YMYMG.KernelAudit
