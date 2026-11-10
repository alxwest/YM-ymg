import Temperedness

set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory
open scoped Topology
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

private theorem schwinger_comp (n : ℕ) (T : NPointDomain 3 n → NPointDomain 3 n)
    (hT : MeasurePreserving T) (hTi : MeasurableEmbedding T)
    (hK : ∀ x, targetKernel F n (T x) = targetKernel F n x)
    (f g : ZeroDiagonalSchwartz 3 n) (hfg : ∀ x, g.1 x = f.1 (T x)) :
    schwinger F n f = schwinger F n g := by
  unfold schwinger
  rw [← hT.integral_comp hTi (fun x => (targetKernel F n x : ℂ) * f.1 x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; erw [hK x, hfg x]

theorem E1_translation_invariant (n : ℕ) (a : SpacetimeDim 3)
    (f g : ZeroDiagonalSchwartz 3 n)
    (hfg : ∀ x, g.1 x = f.1 (fun i => x i + a)) :
    schwinger F n f = schwinger F n g := by
  have hT := translateNPoint_measurePreserving (d := 3) (n := n) a
  exact schwinger_comp F n _ hT
    (hT.measurable.measurableEmbedding (fun x y h => funext fun i =>
      add_right_cancel (congrFun h i)))
    (fun x => targetKernel_translation F n x a) f g hfg

theorem E3_symmetric (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : ZeroDiagonalSchwartz 3 n)
    (hfg : ∀ x, g.1 x = f.1 (fun i => x (σ i))) :
    schwinger F n f = schwinger F n g := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => SpacetimeDim 3) σ.symm
  have he (x : NPointDomain 3 n) : e x = x ∘ σ := by
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n => SpacetimeDim 3) σ.symm x (σ i)
    simpa only [Equiv.symm_apply_apply, e, Function.comp_def] using h
  apply schwinger_comp F n e
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => SpacetimeDim 3) σ.symm)
    e.measurableEmbedding
  · intro x; rw [he]; exact targetKernel_permutation F n x σ
  · intro x; rw [he]; exact hfg x

theorem E0_reality (n : ℕ) (f g : ZeroDiagonalSchwartz 3 n)
    (hfg : ∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN 3 x))) :
    starRingEnd ℂ (schwinger F n f) = schwinger F n g := by
  have hT := timeReflectionN_measurePreserving (d := 3) (n := n)
  have hi : Function.Involutive (timeReflectionN (n := n) 3) := by
    intro x; funext i; exact timeReflection_timeReflection 3 (x i)
  unfold schwinger
  rw [← integral_conj, ← hT.integral_comp
    (hT.measurable.measurableEmbedding hi.injective)
    (fun x => starRingEnd ℂ ((targetKernel F n x : ℂ) * f.1 x))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [targetKernel_reflection F n x, hfg x, map_mul, Complex.conj_ofReal]

def matrixOrtho (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : R.transpose * R = 1) : Ortho :=
  ⟨R, by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hR⟩

def transportedOrtho (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : R.transpose * R = 1) : Ortho :=
  matrixOrtho (R.submatrix axisSwap axisSwap) (by
    change R.transpose.submatrix axisSwap axisSwap * R.submatrix axisSwap axisSwap = 1
    rw [Matrix.submatrix_mul_equiv, hR, Matrix.submatrix_one_equiv])

theorem pointEquiv_rotation (R : Matrix (Fin 4) (Fin 4) ℝ)
    (hR : R.transpose * R = 1) (x : SpacetimeDim 3) :
    pointEquiv (R.mulVec x) = Ortho.move (transportedOrtho R hR) (pointEquiv x) := by
  apply PiLp.ext
  intro i
  change (R.mulVec x) (axisSwap i) =
    ((R.submatrix axisSwap axisSwap).mulVec (x ∘ axisSwap)) i
  rw [Matrix.submatrix_mulVec_equiv]
  simp [axisSwap, Function.comp_def]

theorem targetKernel_rotation (n : ℕ) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (hR : R.transpose * R = 1) (x : NPointDomain 3 n) :
    targetKernel F n (fun i => R.mulVec (x i)) = targetKernel F n x := by
  classical
  have hinj : Function.Injective R.mulVec := by
    intro x y h
    have h' := congrArg (Matrix.mulVec R.transpose) h
    simpa only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec] using h'
  have hi : Function.Injective (fun i => R.mulVec (x i)) ↔ Function.Injective x :=
    hinj.of_comp_iff x
  have hc : configEquiv n (fun i => R.mulVec (x i)) =
      Points.move (transportedOrtho R hR) (configEquiv n x) := by
    apply PiLp.ext; intro i; exact pointEquiv_rotation R hR (x i)
  by_cases hx : Function.Injective x
  · simp only [targetKernel, if_pos hx, if_pos (hi.mpr hx), hc]
    rw [scalarKernel_rotation F _ ((configEquiv_conf x).mpr hx)]
  · simp only [targetKernel, if_neg hx, if_neg (fun h => hx (hi.mp h))]

theorem matrix_measurePreserving (R : Matrix (Fin 4) (Fin 4) ℝ)
    (hR : R.transpose * R = 1) : MeasurePreserving R.mulVec :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).comp
    ((Ortho.motion (matrixOrtho R hR)).measurePreserving.comp
      (PiLp.volume_preserving_toLp (Fin 4)))

/-- Stronger than the target's SO(4) clause: all orthogonal matrices are allowed. -/
theorem E1_rotation_invariant (n : ℕ) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (hR : R.transpose * R = 1) (f g : ZeroDiagonalSchwartz 3 n)
    (hfg : ∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) :
    schwinger F n f = schwinger F n g := by
  have hT : MeasurePreserving (fun x : NPointDomain 3 n => fun i => R.mulVec (x i)) :=
    volume_preserving_pi (fun _ => matrix_measurePreserving R hR)
  have hinj : Function.Injective R.mulVec := by
    intro x y h
    have h' := congrArg (Matrix.mulVec R.transpose) h
    simpa only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec] using h'
  apply schwinger_comp F n _ hT
    (hT.measurable.measurableEmbedding (fun x y h => funext fun i => hinj (congrFun h i)))
  · exact targetKernel_rotation F n R hR
  · exact hfg

theorem normalized_zero (f : ZeroDiagonalSchwartz 3 0) : schwinger F 0 f = f.1 0 := by
  have hK (x : NPointDomain 3 0) : targetKernel F 0 x = 1 := by
    simp only [targetKernel, if_pos (Function.injective_of_subsingleton _), scalarKernel_zero,
      Complex.one_re]
  simp only [schwinger, hK, Complex.ofReal_one, one_mul]
  rw [Measure.volume_pi_eq_dirac (0 : NPointDomain 3 0), integral_dirac]

theorem centered_one (f : ZeroDiagonalSchwartz 3 1) : schwinger F 1 f = 0 := by
  have hK (x : NPointDomain 3 1) : targetKernel F 1 x = 0 := by
    simp only [targetKernel, if_pos (Function.injective_of_subsingleton _), scalarKernel_one,
      Complex.zero_re]
  simp only [schwinger, hK, Complex.ofReal_zero, zero_mul, integral_zero]

#print axioms E0_reality
#print axioms E1_translation_invariant
#print axioms E1_rotation_invariant
#print axioms E3_symmetric
#print axioms normalized_zero
end YMOSBridge
