import Coordinates
import ImportedDiagonalFlatBounds

set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory YangMills.Analysis
open scoped Topology ContDiff
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- Zero on diagonals is an explicit harmless totalization, not a contact-term claim. -/
def targetKernel (n : ℕ) (x : NPointDomain 3 n) : ℝ := by
  classical
  exact if Function.Injective x then (scalarKernel F n (configEquiv n x)).re else 0

theorem targetKernel_eq {n : ℕ} (x : NPointDomain 3 n) (hx : Function.Injective x) :
    (targetKernel F n x : ℂ) = scalarKernel F n (configEquiv n x) := by
  simp only [targetKernel, if_pos hx]
  exact Complex.conj_eq_iff_re.mp (scalarKernel_real F _ ((configEquiv_conf x).mpr hx))

theorem targetKernel_measurable (n : ℕ) : Measurable (targetKernel F n) := by
  classical
  have h : ContinuousOn (fun x : NPointDomain 3 n =>
      (scalarKernel F n (configEquiv n x)).re) {x | Function.Injective x} :=
    Complex.continuous_re.comp_continuousOn
      ((scalarKernel_smooth F n).continuousOn.comp (configEquiv n).continuous.continuousOn
        (fun x hx => (configEquiv_conf x).mpr hx))
  exact h.measurable_piecewise continuousOn_const (sourceConfig_open n).measurableSet

def coincidencePairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2

def separation {n : ℕ} (x : NPointDomain 3 n) : ℝ :=
  affineCoincidenceSeparation (coincidencePairs n) (fun _ _ => 0) x

theorem separation_positive {n : ℕ} (x : NPointDomain 3 n) (hx : Function.Injective x) :
    0 < separation x := by
  apply affineCoincidenceSeparation_pos
  intro p hp
  simpa using hx.ne (show p.1 ≠ p.2 from (Finset.mem_filter.mp hp).2)

theorem separation_le_one {n : ℕ} (x : NPointDomain 3 n) : separation x ≤ 1 :=
  affineCoincidenceSeparation_le_one ..

theorem separation_spaced {n : ℕ} (x : NPointDomain 3 n) :
    spaced (separation x) (configEquiv n x) := by
  intro i j hij
  rw [configEquiv_apply, configEquiv_apply, pointEquiv_cube]
  have h := affineCoincidenceSeparation_le (coincidencePairs n) (fun _ _ => 0) x
    (i := i) (j := j) (by simp [coincidencePairs, hij])
  simpa only [add_zero, separation] using h

/-- The submitted capped bound gives an actual bound on this same selected kernel. -/
theorem targetKernel_bound (n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : NPointDomain 3 n, Function.Injective x →
        ‖targetKernel F n x‖ ≤ B * (separation x ^ N)⁻¹ := by
  obtain ⟨A, B, hB, hbound⟩ := scalarKernel_capped F n 0
  refine ⟨A + 1, by omega, B, hB, ?_⟩
  intro x hx
  have hδ := separation_positive x hx
  have hδ1 := separation_le_one x
  have h := hbound (separation x) hδ hδ1 (configEquiv n x) (separation_spaced x)
  rw [norm_iteratedFDeriv_zero] at h
  calc
    ‖targetKernel F n x‖ = ‖scalarKernel F n (configEquiv n x)‖ := by
      rw [← targetKernel_eq F x hx, Complex.norm_real]
    _ ≤ B * (separation x)⁻¹ ^ A := h
    _ ≤ B * (separation x)⁻¹ ^ (A + 1) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact pow_le_pow_right₀ ((one_le_inv₀ hδ).mpr hδ1) (by omega)
    _ = B * (separation x ^ (A + 1))⁻¹ := by rw [inv_pow]

theorem targetKernel_translation (n : ℕ) (x : NPointDomain 3 n) (a : SpacetimeDim 3) :
    targetKernel F n (fun i => x i + a) = targetKernel F n x := by
  classical
  have hi : Function.Injective (fun i => x i + a) ↔ Function.Injective x := by
    constructor
    · intro h i j hij; exact h (congrArg (fun z => z + a) hij)
    · intro h i j hij; exact h (add_right_cancel hij)
  by_cases hx : Function.Injective x
  · simp only [targetKernel, if_pos hx, if_pos (hi.mpr hx), configEquiv_translation]
    rw [scalarKernel_translation F _ ((configEquiv_conf x).mpr hx)]
  · simp only [targetKernel, if_neg hx, if_neg (fun h => hx (hi.mp h))]

theorem targetKernel_permutation (n : ℕ) (x : NPointDomain 3 n) (σ : Equiv.Perm (Fin n)) :
    targetKernel F n (x ∘ σ) = targetKernel F n x := by
  classical
  have hi : Function.Injective (x ∘ σ) ↔ Function.Injective x := by
    constructor
    · intro h i j hij
      exact σ.symm.injective (h (by simpa using hij))
    · intro h; exact h.comp σ.injective
  by_cases hx : Function.Injective x
  · simp only [targetKernel, if_pos hx, if_pos (hi.mpr hx), configEquiv_permutation]
    rw [scalarKernel_permutation F _ ((configEquiv_conf x).mpr hx)]
  · simp only [targetKernel, if_neg hx, if_neg (fun h => hx (hi.mp h))]

theorem targetKernel_reflection (n : ℕ) (x : NPointDomain 3 n) :
    targetKernel F n (timeReflectionN 3 x) = targetKernel F n x := by
  classical
  have hinj : Function.Injective (timeReflection 3) :=
    (show Function.Involutive (timeReflection 3) from timeReflection_timeReflection 3).injective
  have hi : Function.Injective (timeReflectionN 3 x) ↔ Function.Injective x :=
    hinj.of_comp_iff x
  by_cases hx : Function.Injective x
  · simp only [targetKernel, if_pos hx, if_pos (hi.mpr hx), configEquiv_reflection]
    rw [scalarKernel_rotation F _ ((configEquiv_conf x).mpr hx)]
  · simp only [targetKernel, if_neg hx, if_neg (fun h => hx (hi.mp h))]

#print axioms targetKernel_bound
end YMOSBridge
