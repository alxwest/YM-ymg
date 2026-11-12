import WeakLocalTransport
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! A fixed invertible relabelling represents the rank-one output correction.
Every new output coordinate uses only two old, fixed coordinates. This avoids
assuming locally uniform support for the native mixing coefficients. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.MixingTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion
open YMYMG.DictionaryRenormalization
variable {G : CompactSimpleGaugeGroup}

def labelShear (D : Direction G) (hq : D.weight D.lower = 0) :
    InvariantInsertionLabel G ≃ₗ[ℝ] InvariantInsertionLabel G where
  toFun p := p + D.weight p • D.lower
  invFun p := p - D.weight p • D.lower
  left_inv p := by simp [map_add, map_smul, hq]
  right_inv p := by simp [map_sub, map_smul, hq]
  map_add' p r := by simp only [map_add, add_smul]; abel
  map_smul' c p := by simp [smul_add, smul_smul]

theorem labelShear_weight (D : Direction G) (hq : D.weight D.lower = 0)
    (p : InvariantInsertionLabel G) :
    D.weight (labelShear D hq p) = D.weight p := by
  simp [labelShear, map_add, map_smul, hq]

theorem labelShear_filtered (D : Direction G) (hq : D.weight D.lower = 0)
    (p : InvariantInsertionLabel G) :
    intrinsicEngineeringDimension (labelShear D hq p) ≤ intrinsicEngineeringDimension p := by
  by_cases hp : D.weight p = 0
  · simp [labelShear, hp]
  · exact intrinsicEngineeringDimension_add_le p _ _ le_rfl
      (intrinsicEngineeringDimension_smul_le _ _ _ (D.filtered p hp))

theorem labelShear_symm_filtered (D : Direction G) (hq : D.weight D.lower = 0)
    (p : InvariantInsertionLabel G) :
    intrinsicEngineeringDimension ((labelShear D hq).symm p) ≤
      intrinsicEngineeringDimension p := by
  by_cases hp : D.weight p = 0
  · simp [labelShear, hp]
  · change intrinsicEngineeringDimension (p - D.weight p • D.lower) ≤ _
    rw [sub_eq_add_neg, ← neg_smul]
    exact intrinsicEngineeringDimension_add_le p _ _ le_rfl
      (intrinsicEngineeringDimension_smul_le _ _ _ (D.filtered p hp))

theorem labelShear_dimension (D : Direction G) (hq : D.weight D.lower = 0)
    (p : InvariantInsertionLabel G) :
    intrinsicEngineeringDimension (labelShear D hq p) = intrinsicEngineeringDimension p := by
  apply le_antisymm (labelShear_filtered D hq p)
  simpa only [LinearEquiv.symm_apply_apply] using
    labelShear_symm_filtered D hq (labelShear D hq p)

def pushLabels (D : Direction G) (hq : D.weight D.lower = 0) :
    (InvariantInsertionLabel G →₀ ℝ) ≃ₗ[ℝ] (InvariantInsertionLabel G →₀ ℝ) :=
  Finsupp.domLCongr (labelShear D hq).toEquiv

theorem pushLabels_apply (D : Direction G) (hq : D.weight D.lower = 0)
    (c : InvariantInsertionLabel G →₀ ℝ) (p : InvariantInsertionLabel G) :
    pushLabels D hq c p = c ((labelShear D hq).symm p) := by
  rfl

def outputDifference (D : Direction G) (hq : D.weight D.lower = 0) :
    (InvariantInsertionLabel G →₀ ℝ) →ₗ[ℝ] (InvariantInsertionLabel G →₀ ℝ) :=
  (pushLabels D hq).toLinearMap - LinearMap.id

theorem outputDifference_apply (D : Direction G) (hq : D.weight D.lower = 0)
    (c : InvariantInsertionLabel G →₀ ℝ) (p : InvariantInsertionLabel G) :
    outputDifference D hq c p = c ((labelShear D hq).symm p) - c p := rfl

theorem outputDifference_filtered (D : Direction G) (hq : D.weight D.lower = 0)
    (c : InvariantInsertionLabel G →₀ ℝ) (bound : ℕ)
    (hc : ∀ p, c p ≠ 0 → intrinsicEngineeringDimension p ≤ bound)
    (p : InvariantInsertionLabel G) (hp : outputDifference D hq c p ≠ 0) :
    intrinsicEngineeringDimension p ≤ bound := by
  by_cases hp0 : c p = 0
  · have hi : c ((labelShear D hq).symm p) ≠ 0 := by
      simpa only [outputDifference_apply, hp0, sub_zero] using hp
    have hd := (labelShear_filtered D hq ((labelShear D hq).symm p)).trans (hc _ hi)
    simpa only [LinearEquiv.apply_symm_apply] using hd
  · exact hc p hp0

theorem outputDifference_smooth (D : Direction G) (hq : D.weight D.lower = 0)
    (c : ℝ → InvariantInsertionLabel G →₀ ℝ)
    (hc : ∀ p, ContDiffOn ℝ ∞ (fun mu => c mu p) (Set.Ioi 0))
    (p : InvariantInsertionLabel G) :
    ContDiffOn ℝ ∞ (fun mu => outputDifference D hq (c mu) p) (Set.Ioi 0) := by
  exact (hc ((labelShear D hq).symm p)).sub (hc p)

theorem outputDifference_evaluate {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Direction G) (hq : D.weight D.lower = 0)
    (J : InvariantInsertionLabel G →ₗ[ℝ] V) (c : InvariantInsertionLabel G →₀ ℝ) :
    Finsupp.linearCombination ℝ J (outputDifference D hq c) =
      (Finsupp.linearCombination ℝ D.weight c) • J D.lower := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_smul]
  | single p a =>
    simp only [outputDifference, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply, map_sub, pushLabels, Finsupp.domLCongr_single,
      Finsupp.linearCombination_single]
    simp [labelShear, map_add, map_smul, smul_add, smul_smul]

def differenceMixing (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0) : CompositeMixing G where
  coefficient mu r l p := outputDifference D hq (K.coefficient mu r l p)
  filtered mu r l p q h := outputDifference_filtered D hq _ _
    (K.filtered mu r l p) q h
  smooth r l p q := outputDifference_smooth D hq _ (K.smooth r l p) q
  classical mu r p hmu := by rw [K.classical mu r p hmu, map_zero]
  unit mu r l hmu := by rw [K.unit mu r l hmu, map_zero]
  linear_add mu r l p q := by rw [K.linear_add, map_add]
  linear_smul mu r l c p := by rw [K.linear_smul, map_smul]

theorem differenceMixing_graph (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0)
    (hK : ∀ mu r l p, 0 < mu → r < 2*l → K.coefficient mu r l p = 0) :
    ∀ mu r l p, 0 < mu → r < 2*l →
      (differenceMixing K D hq).coefficient mu r l p = 0 := by
  intro mu r l p hmu hrl
  simp only [differenceMixing, hK mu r l p hmu hrl, map_zero]

#print axioms labelShear
#print axioms labelShear_weight
#print axioms labelShear_filtered
#print axioms labelShear_symm_filtered
#print axioms labelShear_dimension
#print axioms pushLabels_apply
#print axioms outputDifference_apply
#print axioms outputDifference_filtered
#print axioms outputDifference_smooth
#print axioms outputDifference_evaluate
#print axioms differenceMixing
#print axioms differenceMixing_graph
end YMYMG.MixingTransport
