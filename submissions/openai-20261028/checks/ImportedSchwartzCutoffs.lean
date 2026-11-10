import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Sequences
import ImportedSchwartzDomain

/-! Supported Schwartz approximation.

The implementation establishes O(1/R) bounds in every Schwartz seminorm,
then compact strict approximation and actual supported product-span density.
All full derivative flatness hypotheses include the boundary itself.
-/

open Filter Set
open scoped Topology BigOperators ContDiff

noncomputable section

universe u

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_iteratedFDeriv_dilate_le (χ : SchwartzMap E ℝ)
    {r : ℝ} (hr : ‖r‖ ≤ 1) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => χ (r • y)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n χ := by
  let L : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ 1 := by
    calc
      ‖L‖ = ‖r‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul _ _
      _ ≤ 1 * 1 := mul_le_mul hr ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := mul_one _
  change ‖iteratedFDeriv ℝ n ((χ : E → ℝ) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (χ.smooth ⊤) x (mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n χ (L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ SchwartzMap.seminorm ℝ 0 n χ * 1 := by
      gcongr
      · exact norm_iteratedFDeriv_le_seminorm ℝ χ n (L x)
      · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          pow_le_one₀ (norm_nonneg L) hL (n := n)
    _ = _ := mul_one _

private theorem norm_iteratedFDeriv_dilate_sub_one_le (χ : SchwartzMap E ℝ)
    {r : ℝ} (hr : ‖r‖ ≤ 1) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => χ (r • y) - 1) x‖ ≤ SchwartzMap.seminorm ℝ 0 n χ + 1 := by
  have hs : ContDiff ℝ n (fun y => χ (r • y)) :=
    (χ.smooth n).comp (contDiff_const.smul contDiff_id)
  change ‖iteratedFDeriv ℝ n ((fun y => χ (r • y)) - (fun _ : E => (1 : ℝ))) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (g := fun _ : E => (1 : ℝ)) hs.contDiffAt contDiff_const.contDiffAt]
  apply (norm_sub_le _ _).trans
  apply add_le_add (norm_iteratedFDeriv_dilate_le χ hr n x)
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_succ_const]

private theorem weighted_derivative_le_inv_mul_seminorm (f : SchwartzMap E F)
    {R : ℝ} (hR : 0 < R) {x : E} (hx : R ≤ ‖x‖) (k n : ℕ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ R⁻¹ * SchwartzMap.seminorm ℝ (k + 1) n f := by
  rw [inv_mul_eq_div, le_div_iff₀ hR]
  calc
    _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) * ‖x‖ := by gcongr
    _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f x‖ := by ring
    _ ≤ _ := le_seminorm ℝ (k + 1) n f x

private theorem dilate_hasTemperateGrowth (χ : SchwartzMap E ℝ) (r : ℝ) :
    Function.HasTemperateGrowth (fun x => χ (r • x)) := by
  exact χ.hasTemperateGrowth.comp
    (r • ContinuousLinearMap.id ℝ E).hasTemperateGrowth

/-- Every weighted derivative of a cutoff error is controlled by one additional
Schwartz decay weight. The cutoff derivative constants do not depend on R. -/
theorem seminorm_dilateCutoff_sub_le (χ : SchwartzMap E ℝ)
    (hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1) (f : SchwartzMap E F)
    {R : ℝ} (hR : 1 ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
        (smulLeftCLM F (fun x => χ (R⁻¹ • x)) f - f) ≤
      R⁻¹ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℝ 0 i χ + 1) *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) f := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRi : ‖R⁻¹‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hRp.le)]
    exact inv_le_one_of_one_le₀ hR
  let g : E → ℝ := fun x => χ (R⁻¹ • x) - 1
  have hg : ContDiff ℝ ∞ g :=
    ((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id)).sub contDiff_const
  have heq : (⇑(smulLeftCLM F (fun x => χ (R⁻¹ • x)) f - f) : E → F) =
      fun x => g x • f x := by
    funext x
    rw [sub_apply, smulLeftCLM_apply_apply (dilate_hasTemperateGrowth χ _)]
    simp [g, sub_smul]
  apply seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  rw [heq]
  by_cases hx : ‖x‖ < R
  · have hz : (fun y => g y • f y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [continuous_norm.continuousAt.eventually_lt_const hx] with y hy
      have hnorm : ‖R⁻¹ • y‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hRp.le), inv_mul_eq_div]
        exact (div_le_one hRp).mpr hy.le
      simp [g, hχ _ hnorm]
    have hz' := (hz.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
    rw [hz']
    have hzero : iteratedFDeriv ℝ n (fun _ : E => (0 : F)) x = 0 :=
      congrFun iteratedFDeriv_zero x
    rw [hzero, norm_zero, mul_zero]
    positivity
  · have hnorm : R ≤ ‖x‖ := le_of_not_gt hx
    have hb := norm_iteratedFDeriv_smul_le hg (f.smooth ⊤) x (n := n)
      (mod_cast le_top)
    calc
      _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i g x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (SchwartzMap.seminorm ℝ 0 i χ + 1) *
            (R⁻¹ * SchwartzMap.seminorm ℝ (k + 1) (n - i) f) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_dilate_sub_one_le χ hRi i x) (Nat.cast_nonneg _)
        · exact weighted_derivative_le_inv_mul_seminorm f hRp hnorm k (n - i)
        · positivity
        · positivity
      _ = _ := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring

/-- Dilating a smooth radial cutoff to infinity converges to the identity on
Schwartz space, including all weighted derivatives. -/
theorem tendsto_smulLeftCLM_dilate (χ : SchwartzMap E ℝ)
    (hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1) (f : SchwartzMap E F) :
    Tendsto (fun R : ℝ => smulLeftCLM F (fun x => χ (R⁻¹ • x)) f)
      atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds_atTop]
  rintro ⟨k, n⟩ ε hε
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ 0 i χ + 1) * SchwartzMap.seminorm ℝ (k + 1) (n - i) f
  refine ⟨max 1 ((C + 1) / ε), fun R hR => ?_⟩
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRC : C + 1 ≤ R * ε :=
    (div_le_iff₀ hε).mp ((le_max_right _ _).trans hR)
  apply (seminorm_dilateCutoff_sub_le χ hχ f hR1 k n).trans_lt
  change R⁻¹ * C < ε
  rw [inv_mul_eq_div, div_lt_iff₀ hRp]
  linarith

theorem hasCompactSupport_dilateCutoff (χ : SchwartzMap E ℝ)
    (hχc : HasCompactSupport (χ : E → ℝ)) (f : SchwartzMap E F)
    {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (smulLeftCLM F (fun x => χ (R⁻¹ • x)) f : E → F) := by
  rw [smulLeftCLM_apply (dilate_hasTemperateGrowth χ _)]
  exact (hχc.comp_smul (inv_ne_zero hR)).smul_right

theorem exists_compactCutoff_sequence [FiniteDimensional ℝ E]
    (f : SchwartzMap E F) :
    ∃ g : ℕ → SchwartzMap E F,
      (∀ j, HasCompactSupport (g j : E → F)) ∧ Tendsto g atTop (𝓝 f) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : SchwartzMap E ℝ := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1 := by
    intro x hx
    exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, b] using hx)
  refine ⟨fun j => smulLeftCLM F (fun x => χ (((j : ℝ) + 1)⁻¹ • x)) f, ?_, ?_⟩
  · intro j
    exact hasCompactSupport_dilateCutoff χ b.hasCompactSupport f (by positivity)
  · exact (tendsto_smulLeftCLM_dilate χ hχ f).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end SchwartzMap
