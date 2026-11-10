import SourceScalar
import YangMills.OSRecon.Vendored.Axioms

set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory
open scoped Topology ContDiff

def axisSwap : Equiv.Perm (Fin 4) := Equiv.swap 0 3

def pointLinear : SpacetimeDim 3 ≃ₗ[ℝ] E4 where
  toFun x := WithLp.toLp 2 (x ∘ axisSwap)
  invFun x := x.ofLp ∘ axisSwap
  left_inv x := by ext j; simp [axisSwap]
  right_inv x := by ext j; simp [axisSwap]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pointEquiv : SpacetimeDim 3 ≃L[ℝ] E4 := pointLinear.toContinuousLinearEquiv

def configEquiv (n : ℕ) : NPointDomain 3 n ≃L[ℝ] Points n :=
  (ContinuousLinearEquiv.piCongrRight fun _ => pointEquiv).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)).symm

@[simp] theorem configEquiv_apply {n : ℕ} (x : NPointDomain 3 n) (i : Fin n) :
    configEquiv n x i = pointEquiv (x i) := rfl

@[simp] theorem pointEquiv_time (x : SpacetimeDim 3) : pointEquiv x timeAxis = x 0 := by
  change x (axisSwap 3) = x 0
  simp [axisSwap]

theorem configEquiv_conf {n : ℕ} (x : NPointDomain 3 n) :
    configEquiv n x ∈ conf n ↔ Function.Injective x := by
  constructor
  · intro h i j hij
    exact h (congrArg pointEquiv hij)
  · intro h i j hij
    exact h (pointEquiv.injective hij)

theorem sourceConfig_open (n : ℕ) :
    IsOpen {x : NPointDomain 3 n | Function.Injective x} := by
  have he : {x : NPointDomain 3 n | Function.Injective x} =
      (configEquiv n) ⁻¹' conf n := by ext x; exact (configEquiv_conf x).symm
  rw [he]
  exact (conf_open n).preimage (configEquiv n).continuous

theorem configEquiv_translation {n : ℕ} (x : NPointDomain 3 n) (a : SpacetimeDim 3) :
    configEquiv n (fun i => x i + a) = Points.across (pointEquiv a) (configEquiv n x) := by
  apply PiLp.ext
  intro i
  exact pointEquiv.map_add _ _

theorem configEquiv_permutation {n : ℕ} (x : NPointDomain 3 n) (σ : Equiv.Perm (Fin n)) :
    configEquiv n (x ∘ σ) = Points.rearrange σ (configEquiv n x) := rfl

theorem pointEquiv_cube (x y : SpacetimeDim 3) :
    cubedist (pointEquiv x) (pointEquiv y) = ‖x - y‖ := by
  change dist (x ∘ axisSwap) (y ∘ axisSwap) = ‖x - y‖
  rw [dist_eq_norm]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm (x - y) (axisSwap i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := norm_le_pi_norm ((x ∘ axisSwap) - (y ∘ axisSwap)) (axisSwap i)
    simpa [axisSwap] using h

theorem pointEquiv_reflection (x : SpacetimeDim 3) :
    pointEquiv (timeReflection 3 x) = Ortho.move (Signed.reflect timeAxis) (pointEquiv x) := by
  apply PiLp.ext
  intro j
  fin_cases j <;> norm_num [pointEquiv, pointLinear, axisSwap,
    timeReflection, timeAxis, Equiv.swap_apply_def, Fin.ext_iff]

theorem configEquiv_reflection {n : ℕ} (x : NPointDomain 3 n) :
    configEquiv n (timeReflectionN 3 x) =
      Points.move (Signed.reflect timeAxis) (configEquiv n x) := by
  apply PiLp.ext
  intro i
  exact pointEquiv_reflection (x i)
end YMOSBridge
