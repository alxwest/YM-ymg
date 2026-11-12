import YMGSubmission.PublicTheory
import YangMills.QFT.Spacetime

set_option autoImplicit false
set_option warningAsError true

/-!
The October source uses Euclidean four-vectors with time in the last slot.
ym-lean uses four real coordinates with time in the first slot. This module
transports the actual coordinate and Schwartz spaces, including the forward
cone and spacelike relation. It proves no field, Hamiltonian, or matching
existence assertion.
-/

noncomputable section
namespace YMYMG.SpacetimeTransport

def coordinatesLinear : YMGSubmission.Spacetime ≃ₗ[ℝ] YangMills.Spacetime where
  toFun x := ![x 3, x 0, x 1, x 2]
  invFun x := WithLp.toLp 2 ![x 1, x 2, x 3, x 0]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> rfl

def coordinates : YMGSubmission.Spacetime ≃L[ℝ] YangMills.Spacetime :=
  coordinatesLinear.toContinuousLinearEquiv

@[simp] theorem time_coordinate (x : YMGSubmission.Spacetime) :
    coordinates x 0 = YMGSubmission.time x := rfl

theorem minkowski_square (x : YMGSubmission.Spacetime) :
    YangMills.minkowski (coordinates x) (coordinates x) =
      YMGSubmission.minkowskiSquare x := by
  unfold YMGSubmission.minkowskiSquare
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [YangMills.minkowski,
    YMGSubmission.time, YMGSubmission.timeAxis, YMGSubmission.spatial,
    coordinates, coordinatesLinear, Fin.sum_univ_succ, pow_two]

theorem forward_cone (x : YMGSubmission.Spacetime) :
    coordinates x ∈ YangMills.FutureCone ↔ x ∈ YMGSubmission.forwardCone := by
  change (0 ≤ coordinates x 0 ∧
    0 ≤ YangMills.minkowski (coordinates x) (coordinates x)) ↔
    ‖YMGSubmission.spatial x‖ ≤ YMGSubmission.time x
  rw [time_coordinate, minkowski_square]
  unfold YMGSubmission.minkowskiSquare
  constructor
  · rintro ⟨ht, hsq⟩
    exact (sq_le_sq₀ (norm_nonneg _) ht).mp (sub_nonneg.mp hsq)
  · intro h
    have ht := (norm_nonneg (YMGSubmission.spatial x)).trans h
    exact ⟨ht, sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) ht).mpr h)⟩

theorem spacelike (x y : YMGSubmission.Spacetime) :
    YangMills.SpacelikeSeparated (coordinates x) (coordinates y) ↔
      x - y ∈ YMGSubmission.spacelike := by
  unfold YangMills.SpacelikeSeparated YMGSubmission.spacelike
  rw [← map_sub coordinates, minkowski_square]
  rfl

def toSourceTest : YangMills.TestFunction →L[ℂ] YMGSubmission.TestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates

def toNativeTest : YMGSubmission.TestFunction →L[ℂ] YangMills.TestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates.symm

@[simp] theorem toSourceTest_apply (f : YangMills.TestFunction)
    (x : YMGSubmission.Spacetime) : toSourceTest f x = f (coordinates x) := rfl

@[simp] theorem toNativeTest_apply (f : YMGSubmission.TestFunction)
    (x : YangMills.Spacetime) : toNativeTest f x = f (coordinates.symm x) := rfl

@[simp] theorem native_source_test (f : YangMills.TestFunction) :
    toNativeTest (toSourceTest f) = f := by
  ext x
  simp

@[simp] theorem source_native_test (f : YMGSubmission.TestFunction) :
    toSourceTest (toNativeTest f) = f := by
  ext x
  simp

end YMYMG.SpacetimeTransport
