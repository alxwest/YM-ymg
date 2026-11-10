import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Sequences
import YangMills.Analysis.SchwartzKernels

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

theorem smulLeftCLM_flat {s : Set E} (f : SchwartzMap E F)
    (hf : ∀ n x, x ∈ s → iteratedFDeriv ℝ n f x = 0)
    {g : E → ℝ} (hg : g.HasTemperateGrowth) :
    ∀ n x, x ∈ s → iteratedFDeriv ℝ n (smulLeftCLM F g f) x = 0 := by
  intro n x hx
  apply norm_le_zero_iff.mp
  rw [smulLeftCLM_apply hg]
  apply (norm_iteratedFDeriv_smul_le hg.1 (f.smooth ⊤) x (mod_cast le_top)).trans
  simp only [hf _ x hx, norm_zero, mul_zero, Finset.sum_const_zero, le_refl]

theorem lineDerivOp_flat {s : Set E} (f : SchwartzMap E F)
    (hf : ∀ n x, x ∈ s → iteratedFDeriv ℝ n f x = 0) (v : E) :
    ∀ n x, x ∈ s →
      iteratedFDeriv ℝ n (LineDeriv.lineDerivOp v f : SchwartzMap E F) x = 0 := by
  intro n x hx
  apply norm_le_zero_iff.mp
  have h := norm_iteratedFDeriv_clm_apply_const
    ((fderivCLM ℝ E F f).smooth n).contDiffAt (x := x) (c := v) le_rfl
  change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ ≤ 0
  apply h.trans
  change ‖v‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ ≤ 0
  rw [norm_iteratedFDeriv_fderiv, hf (n + 1) x hx, norm_zero, mul_zero]

theorem fderivCLM_flat {s : Set E} (f : SchwartzMap E F)
    (hf : ∀ n x, x ∈ s → iteratedFDeriv ℝ n f x = 0) :
    ∀ n x, x ∈ s → iteratedFDeriv ℝ n (fderivCLM ℝ E F f) x = 0 := by
  intro n x hx
  apply norm_eq_zero.mp
  change ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ = 0
  rw [norm_iteratedFDeriv_fderiv, hf (n + 1) x hx, norm_zero]

/-- Flatness at a hyperplane gives arbitrarily high powers of the transverse
coordinate. This form needs no nondegeneracy in the coefficient space. -/
theorem exists_bound_norm_of_flat_hyperplane (τ : E →L[ℝ] ℝ) (v : E)
    (hv : τ v = 1) (N : ℕ) (f : SchwartzMap E F)
    (hf : ∀ n x, τ x = 0 → iteratedFDeriv ℝ n f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 0 ≤ τ x → ‖f x‖ ≤ C * (τ x) ^ N := by
  induction N generalizing f with
  | zero =>
    refine ⟨SchwartzMap.seminorm ℝ 0 0 f + 1, by positivity, fun x hx => ?_⟩
    simpa only [pow_zero, mul_one] using (norm_le_seminorm ℝ f x).trans (by linarith)
  | succ N ih =>
    let g : SchwartzMap E F := LineDeriv.lineDerivOp v f
    have hg : ∀ n x, τ x = 0 → iteratedFDeriv ℝ n g x = 0 :=
      lineDerivOp_flat f hf v
    obtain ⟨C, hC, hbound⟩ := ih g hg
    refine ⟨C, hC, fun x hx => ?_⟩
    let y := x - τ x • v
    have hy : τ y = 0 := by simp [y, hv]
    let γ : ℝ → E := fun t => y + t • v
    have hγ : ∀ t, τ (γ t) = t := by intro t; simp [γ, hy, hv]
    have hγx : γ (τ x) = x := by simp [γ, y]
    have hf0 : f (γ 0) = 0 := by
      have hh := hf 0 (γ 0) (by simp [hγ])
      have hh' : ‖f (γ 0)‖ = 0 := by
        simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm hh
      exact norm_eq_zero.mp hh'
    have hderiv : ∀ t, HasDerivAt (fun t => f (γ t)) (g (γ t)) t := by
      intro t
      have hpath : HasDerivAt γ v t := by
        simpa [γ] using ((hasDerivAt_id t).smul_const v).const_add y
      exact (f.hasFDerivAt (γ t)).comp_hasDerivAt t hpath
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t ∈ Set.Icc 0 (τ x)) => (hderiv t).hasDerivWithinAt)
      (C := C * (τ x) ^ N) (fun t ht =>
        (hbound (γ t) (by simpa [hγ] using ht.1)).trans (by
          rw [hγ]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2.le N) hC.le)) (τ x) (Set.right_mem_Icc.mpr hx)
    simpa only [hγx, hf0, sub_zero, pow_succ, mul_assoc] using hmain

/-- The same arbitrary-order boundary estimate for every full derivative.
The domain and codomain may share any universe; the scalar joint test domains
in the OS application are both in universe zero. -/
theorem exists_bound_norm_iteratedFDeriv_of_flat_hyperplane
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (τ : X →L[ℝ] ℝ) (v : X) (hv : τ v = 1) (N n : ℕ) (f : SchwartzMap X Y)
    (hf : ∀ j x, τ x = 0 → iteratedFDeriv ℝ j f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 0 ≤ τ x →
      ‖iteratedFDeriv ℝ n f x‖ ≤ C * (τ x) ^ N := by
  induction n generalizing Y with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero] using
      exists_bound_norm_of_flat_hyperplane τ v hv N f hf
  | succ n ih =>
    obtain ⟨C, hC, hb⟩ := ih (fderivCLM ℝ X Y f) (fderivCLM_flat f hf)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hh : ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ ≤ C * (τ x) ^ N := hb x hx
    rwa [norm_iteratedFDeriv_fderiv] at hh

theorem exists_weighted_bound_of_compact_flat_hyperplane
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (τ : X →L[ℝ] ℝ) (v : X) (hv : τ v = 1) (N k n : ℕ) (f : SchwartzMap X Y)
    (hfc : HasCompactSupport (f : X → Y))
    (hf : ∀ j x, τ x = 0 → iteratedFDeriv ℝ j f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 0 ≤ τ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * (τ x) ^ N := by
  obtain ⟨R, hRp, hR⟩ := hfc.isBounded.exists_pos_norm_le
  obtain ⟨C, hCp, hC⟩ :=
    exists_bound_norm_iteratedFDeriv_of_flat_hyperplane τ v hv N n f hf
  refine ⟨R ^ k * C, by positivity, fun x hx => ?_⟩
  by_cases hz : iteratedFDeriv ℝ n f x = 0
  · rw [hz, norm_zero, mul_zero]
    positivity
  · have hxs : x ∈ tsupport (f : X → Y) := support_iteratedFDeriv_subset n hz
    calc
      _ ≤ R ^ k * (C * (τ x) ^ N) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg x) (hR x hxs) k
        · exact hC x hx
        · positivity
        · positivity
      _ = _ := by ring

private theorem norm_iteratedFDeriv_schwartz_comp_clm_le
    (χ : SchwartzMap ℝ ℝ) (L : E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n ((χ : ℝ → ℝ) ∘ L) x‖ ≤
      SchwartzMap.seminorm ℝ 0 n χ * ‖L‖ ^ n := by
  rw [L.iteratedFDeriv_comp_right (χ.smooth ⊤) x (mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_le_seminorm ℝ χ n (L x))
      (show 0 ≤ ∏ _ : Fin n, ‖L‖ by positivity)

private theorem cutoff_scale_pow_bound {j t : ℝ} (hj : 1 ≤ j) (ht : 0 ≤ t)
    (hjt : j * t ≤ 2) {i n : ℕ} (hi : i ≤ n) :
    j ^ i * t ^ (n + 1) ≤ j⁻¹ * 2 ^ (n + 1) := by
  have hjp : 0 < j := lt_of_lt_of_le zero_lt_one hj
  rw [inv_mul_eq_div, le_div_iff₀ hjp]
  calc
    _ = j ^ (i + 1) * t ^ (n + 1) := by ring
    _ ≤ j ^ (n + 1) * t ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj (Nat.add_le_add_right hi 1))
        (pow_nonneg ht _)
    _ = (j * t) ^ (n + 1) := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hjp.le ht) hjt _

/-- The shrinking boundary strip has an O(1/j) bound in every Schwartz
seminorm, because flatness absorbs every growing cutoff derivative. -/
theorem exists_seminorm_boundary_strip_bound
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (τ : X →L[ℝ] ℝ) (v : X) (hv : τ v = 1) (χ : SchwartzMap ℝ ℝ)
    (hχ : ∀ t, 2 ≤ t → χ t = 0) (f : SchwartzMap X Y)
    (hfc : HasCompactSupport (f : X → Y))
    (hf : ∀ n x, τ x ≤ 0 → iteratedFDeriv ℝ n f x = 0) (k n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : ℝ, 1 ≤ j →
      SchwartzMap.seminorm ℝ k n
        (smulLeftCLM Y (fun x => χ (j * τ x)) f) ≤ j⁻¹ * K := by
  choose C hCp hC using fun i : ℕ =>
    exists_weighted_bound_of_compact_flat_hyperplane τ v hv (n + 1) k (n - i) f hfc
      (fun l x hx => hf l x hx.le)
  let B : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i χ * ‖τ‖ ^ i
  let K := 2 ^ (n + 1) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * C i
  have hB : ∀ i, 0 ≤ B i := fun i => by dsimp [B]; positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hCp i).le
  refine ⟨K, hK, fun j hj => ?_⟩
  have hjp : 0 < j := lt_of_lt_of_le zero_lt_one hj
  let g : X → ℝ := fun x => χ (j * τ x)
  have hg : g.HasTemperateGrowth := χ.hasTemperateGrowth.comp (j • τ).hasTemperateGrowth
  apply seminorm_le_bound ℝ k n _ (mul_nonneg (inv_nonneg.mpr hjp.le) hK)
  intro x
  rw [smulLeftCLM_apply hg]
  have hb := norm_iteratedFDeriv_smul_le hg.1 (f.smooth ⊤) x (n := n) (mod_cast le_top)
  by_cases hx : τ x ≤ 0
  · have hzero : iteratedFDeriv ℝ n (fun y => g y • f y) x = 0 := by
      apply norm_le_zero_iff.mp
      apply hb.trans
      simp only [hf _ x hx, norm_zero, mul_zero, Finset.sum_const_zero, le_refl]
    rw [hzero, norm_zero, mul_zero]
    exact mul_nonneg (inv_nonneg.mpr hjp.le) hK
  · have hxp : 0 < τ x := lt_of_not_ge hx
    by_cases hstrip : j * τ x ≤ 2
    · have hgD : ∀ i, ‖iteratedFDeriv ℝ i g x‖ ≤ j ^ i * B i := by
        intro i
        apply (norm_iteratedFDeriv_schwartz_comp_clm_le χ (j • τ) i x).trans
        dsimp [B]
        rw [norm_smul, Real.norm_of_nonneg hjp.le, mul_pow]
        exact le_of_eq (by ring)
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
            (j ^ i * B i) * (C i * (τ x) ^ (n + 1)) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hgD i) (Nat.cast_nonneg _)
          · exact hC i x hxp.le
          · positivity
          · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hjp.le _) (hB i))
        _ = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * B i * C i) *
            (j ^ i * (τ x) ^ (n + 1)) := by
          congr 1
          ext i
          ring
        _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * B i * C i) *
            (j⁻¹ * 2 ^ (n + 1)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (cutoff_scale_pow_bound hj hxp.le hstrip (Finset.mem_range_succ_iff.mp hi))
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hCp i).le)
        _ = j⁻¹ * K := by
          dsimp [K]
          rw [← Finset.sum_mul]
          ring
    · have hgt : 2 < j * τ x := lt_of_not_ge hstrip
      have hz : (fun y => g y • f y) =ᶠ[𝓝 x] fun _ => (0 : Y) := by
        filter_upwards [(τ.continuous.const_mul j).continuousAt.eventually_const_lt hgt] with y hy
        simp [g, hχ _ hy.le]
      have hz' := (hz.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
      rw [hz']
      have hzero : iteratedFDeriv ℝ n (fun _ : X => (0 : Y)) x = 0 :=
        congrFun iteratedFDeriv_zero x
      rw [hzero, norm_zero, mul_zero]
      exact mul_nonneg (inv_nonneg.mpr hjp.le) hK

theorem tendsto_smulLeftCLM_boundary_strip
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (τ : X →L[ℝ] ℝ) (v : X) (hv : τ v = 1) (χ : SchwartzMap ℝ ℝ)
    (hχ : ∀ t, 2 ≤ t → χ t = 0) (f : SchwartzMap X Y)
    (hfc : HasCompactSupport (f : X → Y))
    (hf : ∀ n x, τ x ≤ 0 → iteratedFDeriv ℝ n f x = 0) :
    Tendsto (fun j : ℝ => smulLeftCLM Y (fun x => χ (j * τ x)) f) atTop (𝓝 0) := by
  rw [(schwartz_withSeminorms ℝ X Y).tendsto_nhds_atTop]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨K, hK, hbound⟩ := exists_seminorm_boundary_strip_bound τ v hv χ hχ f hfc hf k n
  refine ⟨max 1 ((K + 1) / ε), fun j hj => ?_⟩
  have hj1 : 1 ≤ j := (le_max_left _ _).trans hj
  have hjp : 0 < j := lt_of_lt_of_le zero_lt_one hj1
  have hjK : K + 1 ≤ j * ε :=
    (div_le_iff₀ hε).mp ((le_max_right _ _).trans hj)
  simp only [sub_zero, schwartzSeminormFamily_apply]
  apply (hbound j hj1).trans_lt
  rw [inv_mul_eq_div, div_lt_iff₀ hjp]
  linarith

/-- Remove a shrinking strip about the boundary hyperplane. -/
def boundaryCutoff (τ : E →L[ℝ] ℝ) (χ : SchwartzMap ℝ ℝ)
    (j : ℝ) (f : SchwartzMap E F) : SchwartzMap E F :=
  f - smulLeftCLM F (fun x => χ (j * τ x)) f

theorem boundaryCutoff_apply (τ : E →L[ℝ] ℝ) (χ : SchwartzMap ℝ ℝ)
    (j : ℝ) (f : SchwartzMap E F) (x : E) :
    boundaryCutoff τ χ j f x = (1 - χ (j * τ x)) • f x := by
  have hg : (fun x => χ (j * τ x)).HasTemperateGrowth :=
    χ.hasTemperateGrowth.comp (j • τ).hasTemperateGrowth
  simp only [boundaryCutoff, sub_apply, smulLeftCLM_apply_apply hg, sub_smul, one_smul]

theorem boundaryCutoff_tsupport_subset (τ : E →L[ℝ] ℝ) (χ : SchwartzMap ℝ ℝ)
    (j : ℝ) (f : SchwartzMap E F) :
    tsupport (boundaryCutoff τ χ j f : E → F) ⊆ tsupport (f : E → F) := by
  have heq : (boundaryCutoff τ χ j f : E → F) = fun x => (1 - χ (j * τ x)) • f x :=
    funext (boundaryCutoff_apply τ χ j f)
  rw [heq]
  exact tsupport_smul_subset_right _ _

theorem boundaryCutoff_hasCompactSupport (τ : E →L[ℝ] ℝ) (χ : SchwartzMap ℝ ℝ)
    (j : ℝ) (f : SchwartzMap E F) (hfc : HasCompactSupport (f : E → F)) :
    HasCompactSupport (boundaryCutoff τ χ j f : E → F) :=
  hfc.of_isClosed_subset isClosed_closure (boundaryCutoff_tsupport_subset τ χ j f)

theorem boundaryCutoff_flat {s : Set E} (τ : E →L[ℝ] ℝ) (χ : SchwartzMap ℝ ℝ)
    (j : ℝ) (f : SchwartzMap E F)
    (hf : ∀ n x, x ∈ s → iteratedFDeriv ℝ n f x = 0) :
    ∀ n x, x ∈ s → iteratedFDeriv ℝ n (boundaryCutoff τ χ j f) x = 0 := by
  have hg : (fun x => 1 - χ (j * τ x)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 : ℝ)).sub
      (χ.hasTemperateGrowth.comp (j • τ).hasTemperateGrowth)
  have heq : boundaryCutoff τ χ j f = smulLeftCLM F (fun x => 1 - χ (j * τ x)) f := by
    ext x
    rw [boundaryCutoff_apply, smulLeftCLM_apply_apply hg]
  rw [heq]
  exact smulLeftCLM_flat f hf hg

theorem boundaryCutoff_tsupport_subset_halfspace
    (τ : E →L[ℝ] ℝ) (χ : SchwartzMap ℝ ℝ)
    (hχ : ∀ t, ‖t‖ ≤ 1 → χ t = 1) {j : ℝ} (hj : 0 < j)
    (f : SchwartzMap E F) (hf : ∀ x, τ x ≤ 0 → f x = 0) :
    tsupport (boundaryCutoff τ χ j f : E → F) ⊆ {x | j⁻¹ ≤ τ x} := by
  apply closure_minimal ?_ (isClosed_le continuous_const τ.continuous)
  intro x hx
  by_contra hneg
  have hlt : τ x < j⁻¹ := lt_of_not_ge hneg
  apply hx
  rw [boundaryCutoff_apply]
  by_cases hτ : τ x ≤ 0
  · rw [hf x hτ, smul_zero]
  · have hτp : 0 < τ x := lt_of_not_ge hτ
    have hnorm : ‖j * τ x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg hj.le hτp.le)]
      calc
        _ ≤ j * j⁻¹ := mul_le_mul_of_nonneg_left hlt.le hj.le
        _ = 1 := mul_inv_cancel₀ hj.ne'
    rw [hχ _ hnorm, sub_self, zero_smul]

theorem tendsto_boundaryCutoff
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (τ : X →L[ℝ] ℝ) (v : X) (hv : τ v = 1) (χ : SchwartzMap ℝ ℝ)
    (hχ : ∀ t, 2 ≤ t → χ t = 0) (f : SchwartzMap X Y)
    (hfc : HasCompactSupport (f : X → Y))
    (hf : ∀ n x, τ x ≤ 0 → iteratedFDeriv ℝ n f x = 0) :
    Tendsto (fun j : ℝ => boundaryCutoff τ χ j f) atTop (𝓝 f) := by
  simpa only [boundaryCutoff, sub_zero] using
    tendsto_const_nhds.sub (tendsto_smulLeftCLM_boundary_strip τ v hv χ hχ f hfc hf)

/-- A compact flat test can be approximated by compact tests supported strictly
inside any finite intersection of positive half-spaces. Each approximation
also retains the original support constraint. -/
theorem mem_closure_compact_strict_of_compact_flat
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Type*}
    (S : Finset ι) (τ : ι → X →L[ℝ] ℝ) (v : ι → X)
    (hv : ∀ a ∈ S, τ a (v a) = 1) (f : SchwartzMap X Y)
    (hfc : HasCompactSupport (f : X → Y))
    (hf : ∀ a ∈ S, ∀ n x, τ a x ≤ 0 → iteratedFDeriv ℝ n f x = 0) :
    f ∈ closure {g : SchwartzMap X Y |
      HasCompactSupport (g : X → Y) ∧ tsupport (g : X → Y) ⊆ tsupport (f : X → Y) ∧
        ∀ a ∈ S, tsupport (g : X → Y) ⊆ {x | 0 < τ a x}} := by
  classical
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : SchwartzMap ℝ ℝ := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ1 : ∀ t, ‖t‖ ≤ 1 → χ t = 1 := by
    intro t ht
    exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, b] using ht)
  have hχ0 : ∀ t, 2 ≤ t → χ t = 0 := by
    intro t ht
    apply b.zero_of_le_dist
    simpa [b, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t)] using ht
  induction S using Finset.induction_on generalizing f with
  | empty =>
    apply subset_closure
    exact ⟨hfc, Set.Subset.rfl, by simp⟩
  | @insert a S ha ih =>
    have hvS : ∀ a ∈ S, τ a (v a) = 1 := fun a ha => hv a (Finset.mem_insert_of_mem ha)
    have hfa : ∀ n x, τ a x ≤ 0 → iteratedFDeriv ℝ n f x = 0 :=
      hf a (Finset.mem_insert_self _ _)
    have hvA := hv a (Finset.mem_insert_self _ _)
    have hlim := tendsto_boundaryCutoff (τ a) (v a) hvA χ hχ0 f hfc hfa
    apply isClosed_closure.mem_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with j hj
    let fj := boundaryCutoff (τ a) χ j f
    have hjp : 0 < j := lt_of_lt_of_le zero_lt_one hj
    have hfjc : HasCompactSupport (fj : X → Y) :=
      boundaryCutoff_hasCompactSupport (τ a) χ j f hfc
    have hfjS : ∀ b ∈ S, ∀ n x, τ b x ≤ 0 → iteratedFDeriv ℝ n fj x = 0 := by
      intro b hb
      exact boundaryCutoff_flat (τ a) χ j f (hf b (Finset.mem_insert_of_mem hb))
    have hfjA : tsupport (fj : X → Y) ⊆ {x | 0 < τ a x} := by
      intro x hx
      have hhalf := boundaryCutoff_tsupport_subset_halfspace (τ a) χ hχ1 hjp f
        (fun x hx => norm_eq_zero.mp (by
          simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm (hfa 0 x hx))) hx
      exact lt_of_lt_of_le (inv_pos.mpr hjp) hhalf
    have hclosure := ih hvS fj hfjc hfjS
    apply (closure_mono ?_) hclosure
    intro g hg
    refine ⟨hg.1, hg.2.1.trans (boundaryCutoff_tsupport_subset (τ a) χ j f), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hg.2.1.trans hfjA
    · exact hg.2.2 b hb

/-- Full Schwartz-topology approximation of flat positive tests by compact
strictly supported tests. No initial uniform gap from the boundary is assumed. -/
theorem exists_compact_strict_sequence_of_flat
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Type*}
    (S : Finset ι) (τ : ι → X →L[ℝ] ℝ) (v : ι → X)
    (hv : ∀ a ∈ S, τ a (v a) = 1) (f : SchwartzMap X Y)
    (hf : ∀ a ∈ S, ∀ n x, τ a x ≤ 0 → iteratedFDeriv ℝ n f x = 0) :
    ∃ g : ℕ → SchwartzMap X Y,
      (∀ j, HasCompactSupport (g j : X → Y) ∧
        tsupport (g j : X → Y) ⊆ tsupport (f : X → Y) ∧
        ∀ a ∈ S, tsupport (g j : X → Y) ⊆ {x | 0 < τ a x}) ∧
      Tendsto g atTop (𝓝 f) := by
  apply (mem_closure_iff_seq_limit (s := {g : SchwartzMap X Y |
    HasCompactSupport (g : X → Y) ∧ tsupport (g : X → Y) ⊆ tsupport (f : X → Y) ∧
      ∀ a ∈ S, tsupport (g : X → Y) ⊆ {x | 0 < τ a x}})).mp
  let b : ContDiffBump (0 : X) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : SchwartzMap X ℝ := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1 := by
    intro x hx
    exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, b] using hx)
  have hlim := tendsto_smulLeftCLM_dilate χ hχ f
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let fR := smulLeftCLM Y (fun x => χ (R⁻¹ • x)) f
  have hfRc : HasCompactSupport (fR : X → Y) :=
    hasCompactSupport_dilateCutoff χ b.hasCompactSupport f hRp.ne'
  have hfRs : tsupport (fR : X → Y) ⊆ tsupport (f : X → Y) := by
    rw [smulLeftCLM_apply (dilate_hasTemperateGrowth χ _)]
    exact tsupport_smul_subset_right _ _
  have hfR : ∀ a ∈ S, ∀ n x, τ a x ≤ 0 → iteratedFDeriv ℝ n fR x = 0 := by
    intro a ha
    exact smulLeftCLM_flat f (hf a ha) (dilate_hasTemperateGrowth χ _)
  have hclosure := mem_closure_compact_strict_of_compact_flat S τ v hv fR hfRc hfR
  apply (closure_mono ?_) hclosure
  intro g hg
  exact ⟨hg.1, hg.2.1.trans hfRs, hg.2.2⟩

/-- A positive compact set admits a smooth compact cutoff equal to one there
whose full topological support still lies in the positive half-space. -/
theorem exists_compact_positive_cutoff [FiniteDimensional ℝ E]
    (τ : E →L[ℝ] ℝ) (K : Set E) (hK : IsCompact K)
    (hpos : ∀ x ∈ K, 0 < τ x) :
    ∃ χ : SchwartzMap E ℝ, HasCompactSupport (χ : E → ℝ) ∧
      (∀ x ∈ K, χ x = 1) ∧ tsupport (χ : E → ℝ) ⊆ {x | 0 < τ x} := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_forall_le' τ.continuous.continuousOn hpos
  obtain ⟨M, hM, hMK⟩ := (hK.image τ.continuous).isBounded.exists_pos_norm_le
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : E) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let ρ : SchwartzMap E ℝ := b.hasCompactSupport.toSchwartzMap b.contDiff
  let β : ContDiffBump (M + δ) :=
    ⟨M + δ / 2, M + 3 * δ / 4, by linarith, by linarith⟩
  have hβ : (fun x => β (τ x)).HasTemperateGrowth :=
    (β.hasCompactSupport.hasTemperateGrowth β.contDiff).comp τ.hasTemperateGrowth
  let χ := smulLeftCLM ℝ (fun x => β (τ x)) ρ
  have hχapp : ∀ x, χ x = β (τ x) * ρ x := fun x => smulLeftCLM_apply_apply hβ ρ x
  have hχc : HasCompactSupport (χ : E → ℝ) := by
    rw [smulLeftCLM_apply hβ]
    have hρc : HasCompactSupport (ρ : E → ℝ) := b.hasCompactSupport
    exact hρc.smul_left (f := fun x : E => β (τ x))
  refine ⟨χ, hχc, ?_, ?_⟩
  · intro x hx
    have hτM : τ x ≤ M := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hMK (τ x) (Set.mem_image_of_mem τ hx))
    have hρ : ρ x = 1 :=
      b.one_of_mem_closedBall (by
        simpa [Metric.mem_closedBall, b] using (hRK x hx).trans (by linarith : R ≤ R + 1))
    have hβx : β (τ x) = 1 := by
      apply β.one_of_mem_closedBall
      change |τ x - (M + δ)| ≤ M + δ / 2
      rw [abs_of_nonpos (by linarith)]
      linarith [hδK x hx]
    rw [hχapp, hρ, hβx, mul_one]
  · have hclosed : tsupport (χ : E → ℝ) ⊆ {x | δ / 4 ≤ τ x} := by
      apply closure_minimal ?_ (isClosed_le continuous_const τ.continuous)
      intro x hx
      by_contra hn
      have hτ : τ x < δ / 4 := lt_of_not_ge hn
      have hβx : β (τ x) = 0 := by
        apply β.zero_of_le_dist
        change M + 3 * δ / 4 ≤ |τ x - (M + δ)|
        rw [abs_of_nonpos (by linarith)]
        linarith
      apply hx
      rw [hχapp, hβx, zero_mul]
    intro x hx
    exact lt_of_lt_of_le (by positivity : 0 < δ / 4) (hclosed hx)

/-- The algebraic span of actual products whose individual factors have
topological support in the prescribed open regions. -/
def supportedProductSpan (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    (n : ℕ) (U : Fin n → Set D) : Submodule ℂ (SchwartzMap (Fin n → D) ℂ) :=
  Submodule.span ℂ (GaussianField.complexProductTensor ''
    {fs : Fin n → SchwartzMap D ℂ | ∀ i, tsupport (fs i : D → ℂ) ⊆ U i})

theorem product_cutoff_mem_supportedProductSpan_closure
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    {n : ℕ} (U : Fin n → Set D) (χ : Fin n → SchwartzMap D ℂ)
    (hχ : ∀ i, tsupport (χ i : D → ℂ) ⊆ U i)
    (h : SchwartzMap (Fin n → D) ℂ) :
    smulLeftCLM ℂ (GaussianField.complexProductTensor χ) h ∈
      (supportedProductSpan D n U).topologicalClosure := by
  let P := supportedProductSpan D n U
  let L := smulLeftCLM ℂ (GaussianField.complexProductTensor χ)
  have hmap : productSpan D n ≤ P.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨fs, rfl⟩
    change L (GaussianField.complexProductTensor fs) ∈ P
    apply Submodule.subset_span
    let gs : Fin n → SchwartzMap D ℂ := fun i => smulLeftCLM ℂ (χ i) (fs i)
    refine ⟨gs, ?_, ?_⟩
    · intro i
      change tsupport (smulLeftCLM ℂ (χ i) (fs i) : D → ℂ) ⊆ U i
      rw [smulLeftCLM_apply (χ i).hasTemperateGrowth]
      exact (tsupport_smul_subset_left _ _).trans (hχ i)
    · ext x
      change GaussianField.complexProductTensor gs x = L (GaussianField.complexProductTensor fs) x
      rw [smulLeftCLM_apply_apply (GaussianField.complexProductTensor χ).hasTemperateGrowth]
      simp only [GaussianField.complexProductTensor_apply, gs,
        smulLeftCLM_apply_apply (χ _).hasTemperateGrowth, smul_eq_mul, Finset.prod_mul_distrib]
  have hmap' : Set.MapsTo L (productSpan D n : Set _) (P : Set _) := hmap
  exact hmap'.closure L.continuous (dense_productSpan n h)

theorem compact_strict_mem_supportedProductSpan_closure
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    {n : ℕ} (τ : D →L[ℝ] ℝ) (h : SchwartzMap (Fin n → D) ℂ)
    (hc : HasCompactSupport (h : (Fin n → D) → ℂ))
    (hs : ∀ i : Fin n, tsupport (h : (Fin n → D) → ℂ) ⊆ {x | 0 < τ (x i)}) :
    h ∈ (supportedProductSpan D n (fun _ => {x | 0 < τ x})).topologicalClosure := by
  let K : Fin n → Set D := fun i => (fun x : Fin n → D => x i) '' tsupport (h : _ → ℂ)
  have hKc : ∀ i, IsCompact (K i) := fun i => hc.image (continuous_apply i)
  have hKp : ∀ i, ∀ x ∈ K i, 0 < τ x := by
    intro i x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hs i hy
  choose χR hχRc hχR1 hχRs using fun i => exists_compact_positive_cutoff τ (K i) (hKc i) (hKp i)
  let χ : Fin n → SchwartzMap D ℂ := fun i => postcompCLM Complex.ofRealCLM (χR i)
  have hχs : ∀ i, tsupport (χ i : D → ℂ) ⊆ {x | 0 < τ x} := by
    intro i
    apply Set.Subset.trans (closure_mono ?_) (hχRs i)
    intro x hx hz
    apply hx
    change (↑(χR i x) : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  have hχ1 : ∀ i, ∀ x ∈ K i, χ i x = 1 := by
    intro i x hx
    change (↑(χR i x) : ℂ) = 1
    rw [hχR1 i x hx, Complex.ofReal_one]
  have hprod := product_cutoff_mem_supportedProductSpan_closure
    (fun _ : Fin n => {x | 0 < τ x}) χ hχs h
  have heq : smulLeftCLM ℂ (GaussianField.complexProductTensor χ) h = h := by
    ext x
    rw [smulLeftCLM_apply_apply (GaussianField.complexProductTensor χ).hasTemperateGrowth]
    by_cases hx : h x = 0
    · rw [hx, smul_zero]
    · have hxi : ∀ i, χ i (x i) = 1 := fun i =>
        hχ1 i (x i) (Set.mem_image_of_mem _ (subset_closure hx))
      simp only [GaussianField.complexProductTensor_apply, hxi, Finset.prod_const_one, one_smul]
  rwa [heq] at hprod

/-- Supported product density for the full flat positive-orthant space.
Products are genuine pointwise products and convergence is in the Schwartz
topology, even when the original topological support meets a time boundary. -/
theorem mem_supportedProductSpan_closure_of_flat
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    {n : ℕ} (τ : D →L[ℝ] ℝ) (v : D) (hv : τ v = 1)
    (h : SchwartzMap (Fin n → D) ℂ)
    (hf : ∀ m x, (∃ i : Fin n, τ (x i) ≤ 0) → iteratedFDeriv ℝ m h x = 0) :
    h ∈ (supportedProductSpan D n (fun _ => {x | 0 < τ x})).topologicalClosure := by
  classical
  let τs : Fin n → (Fin n → D) →L[ℝ] ℝ := fun i =>
    τ.comp (ContinuousLinearMap.proj i)
  let vs : Fin n → (Fin n → D) := fun i => Pi.single i v
  have hvs : ∀ i ∈ (Finset.univ : Finset (Fin n)), τs i (vs i) = 1 := by
    intro i hi
    simp [τs, vs, hv]
  obtain ⟨g, hg, hlim⟩ := exists_compact_strict_sequence_of_flat Finset.univ τs vs hvs h
    (fun i _ m x hx => hf m x ⟨i, hx⟩)
  apply (supportedProductSpan D n (fun _ => {x | 0 < τ x})).isClosed_topologicalClosure.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro j
  exact compact_strict_mem_supportedProductSpan_closure τ (g j) (hg j).1
    (fun i => (hg j).2.2 i (Finset.mem_univ i))

theorem exists_supported_product_sequence_of_flat
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    {n : ℕ} (τ : D →L[ℝ] ℝ) (v : D) (hv : τ v = 1)
    (h : SchwartzMap (Fin n → D) ℂ)
    (hf : ∀ m x, (∃ i : Fin n, τ (x i) ≤ 0) → iteratedFDeriv ℝ m h x = 0) :
    ∃ g : ℕ → SchwartzMap (Fin n → D) ℂ,
      (∀ j, g j ∈ supportedProductSpan D n (fun _ => {x | 0 < τ x})) ∧
      Tendsto g atTop (𝓝 h) :=
  mem_closure_iff_seq_limit.mp (mem_supportedProductSpan_closure_of_flat τ v hv h hf)

/-- info: 'SchwartzMap.seminorm_dilateCutoff_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seminorm_dilateCutoff_sub_le
/-- info: 'SchwartzMap.tendsto_smulLeftCLM_dilate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_smulLeftCLM_dilate
/-- info: 'SchwartzMap.exists_compactCutoff_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_compactCutoff_sequence
/-- info: 'SchwartzMap.exists_bound_norm_of_flat_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_bound_norm_of_flat_hyperplane
/-- info: 'SchwartzMap.exists_weighted_bound_of_compact_flat_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_weighted_bound_of_compact_flat_hyperplane
/-- info: 'SchwartzMap.exists_seminorm_boundary_strip_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_seminorm_boundary_strip_bound
/-- info: 'SchwartzMap.tendsto_boundaryCutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_boundaryCutoff
/-- info: 'SchwartzMap.exists_compact_strict_sequence_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_compact_strict_sequence_of_flat
/-- info: 'SchwartzMap.exists_compact_positive_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_compact_positive_cutoff
/-- info: 'SchwartzMap.product_cutoff_mem_supportedProductSpan_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms product_cutoff_mem_supportedProductSpan_closure
/-- info: 'SchwartzMap.compact_strict_mem_supportedProductSpan_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compact_strict_mem_supportedProductSpan_closure
/-- info: 'SchwartzMap.mem_supportedProductSpan_closure_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_supportedProductSpan_closure_of_flat
/-- info: 'SchwartzMap.exists_supported_product_sequence_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_supported_product_sequence_of_flat

end SchwartzMap

namespace EuclideanField

/-- Actual joint products of finite-component tests with supported scalar
components, followed by their algebraic complex linear span. -/
def supportedJointProductSpan (d : ℕ) (I : Type*) [Fintype I] (n : ℕ)
    (U : Fin n → Set (EuclideanSpace ℝ (Fin d))) : Submodule ℂ (JointTest d I n) :=
  Submodule.span ℂ (jointProduct ''
    {fs : Fin n → ComplexTest d I |
      ∀ i a, tsupport (fs i a : EuclideanSpace ℝ (Fin d) → ℂ) ⊆ U i})

theorem mem_supportedJointProductSpan_closure_of_flat
    {d n : ℕ} {I : Type*} [Fintype I] (hd : 0 < d)
    (τ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d))
    (hv : τ v = 1) (h : JointTest d I n)
    (hf : ∀ α m x, (∃ i : Fin n, τ (x i) ≤ 0) → iteratedFDeriv ℝ m (h α) x = 0) :
    h ∈ (supportedJointProductSpan d I n (fun _ => {x | 0 < τ x})).topologicalClosure := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let P := supportedJointProductSpan d I n (fun _ => {x | 0 < τ x})
  let S := SchwartzMap.supportedProductSpan (EuclideanSpace ℝ (Fin d)) n
    (fun _ => {x | 0 < τ x})
  have hsingle (α : Fin n → I) : Pi.single α (h α) ∈ P.topologicalClosure := by
    let L := ContinuousLinearMap.single ℂ
      (fun _ : Fin n → I => SchwartzMap (Fin n → EuclideanSpace ℝ (Fin d)) ℂ) α
    have hmap : S ≤ P.comap L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨fs, hfs, rfl⟩
      change Pi.single α (GaussianField.complexProductTensor fs) ∈ P
      rw [← jointProduct_single]
      apply Submodule.subset_span
      refine ⟨fun i => Pi.single (α i) (fs i), ?_, rfl⟩
      intro i a
      by_cases ha : a = α i
      · subst a
        simpa only [Pi.single_eq_same] using hfs i
      · simp only [Pi.single_eq_of_ne ha, FunLike.coe_zero, tsupport_zero, Set.empty_subset]
    have hmap' : Set.MapsTo L (S : Set _) (P : Set _) := hmap
    exact hmap'.closure L.continuous
      (SchwartzMap.mem_supportedProductSpan_closure_of_flat τ v hv (h α) (hf α))
  have heq : h = ∑ α, Pi.single α (h α) := by ext α x; simp
  rw [heq]
  exact P.topologicalClosure.sum_mem (fun α _ => hsingle α)

theorem exists_supported_joint_product_sequence_of_flat
    {d n : ℕ} {I : Type*} [Fintype I] (hd : 0 < d)
    (τ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d))
    (hv : τ v = 1) (h : JointTest d I n)
    (hf : ∀ α m x, (∃ i : Fin n, τ (x i) ≤ 0) → iteratedFDeriv ℝ m (h α) x = 0) :
    ∃ g : ℕ → JointTest d I n,
      (∀ j, g j ∈ supportedJointProductSpan d I n (fun _ => {x | 0 < τ x})) ∧
      Tendsto g atTop (𝓝 h) :=
  mem_closure_iff_seq_limit.mp (mem_supportedJointProductSpan_closure_of_flat hd τ v hv h hf)

/-- info: 'EuclideanField.mem_supportedJointProductSpan_closure_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_supportedJointProductSpan_closure_of_flat
/-- info: 'EuclideanField.exists_supported_joint_product_sequence_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_supported_joint_product_sequence_of_flat

end EuclideanField
