import YangMills.RenormalizationGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true

/-!
# Why pointwise regulator limits do not transport perturbative jets

This is a scalar counterexample to a proposed general inference, not a
Yang–Mills model or a counterexample to either repository's existence claim.
For each positive regulator r, 1 + g² exp(-r/g) has the constant-one jet to
every order. Removing r at fixed positive g gives 1 + g². That limit still
has the same leading term, but fails the prescribed jet at order two.
Thus even actual all-order finite-regulator asymptotics, coefficient
convergence, and agreement of the leading continuum term do not suffice.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace YMYMG.LimitAudit

def tail (r g : ℝ) : ℂ := Real.exp (-r / g)

def regulated (r g : ℝ) : ℂ := 1 + (g : ℂ) ^ 2 * tail r g

def continuum (g : ℝ) : ℂ := 1 + (g : ℂ) ^ 2

def coefficient (k : ℕ) : ℂ := if k = 0 then 1 else 0

theorem partial_sum (N : ℕ) (g : ℝ) :
    (∑ k ∈ Finset.range (N + 1), (g : ℂ) ^ k * coefficient k) = 1 := by
  simp [coefficient]

theorem tail_ratio_limit (r : ℝ) (hr : 0 < r) (N : ℕ) :
    Tendsto (fun g : ℝ => Real.exp (-r / g) / g ^ N)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast, inv_pow, div_eq_mul_inv,
    mul_comm] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) r hr).comp
      tendsto_inv_nhdsGT_zero

theorem tail_has_zero_jet (r : ℝ) (hr : 0 < r) :
    YangMills.RG.HasPerturbativeJet (tail r) (fun _ => 0) := by
  intro N epsilon hEpsilon
  have h := (tail_ratio_limit r hr N).eventually (gt_mem_nhds hEpsilon)
  obtain ⟨delta, hDelta, hBound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  refine ⟨delta, hDelta, fun g hG hGDelta => ?_⟩
  have hRatio := hBound ⟨hG, hGDelta⟩
  have hRem := (div_lt_iff₀ (pow_pos hG N)).mp hRatio
  simp only [mul_zero, Finset.sum_const_zero, sub_zero, tail,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hRem.le

theorem fixed_regulator_jet (r : ℝ) (hr : 0 < r) :
    YangMills.RG.HasPerturbativeJet (regulated r) coefficient := by
  intro N epsilon hEpsilon
  obtain ⟨delta, hDelta, hBound⟩ := tail_has_zero_jet r hr N epsilon hEpsilon
  refine ⟨min delta 1, lt_min hDelta zero_lt_one, fun g hG hGDelta => ?_⟩
  rw [partial_sum]
  have hTail : ‖tail r g‖ ≤ epsilon * g ^ N := by
    simpa using hBound g hG (lt_of_lt_of_le hGDelta (min_le_left _ _))
  have hGOne : g ≤ 1 := (lt_of_lt_of_le hGDelta (min_le_right _ _)).le
  calc
    ‖regulated r g - 1‖ = g ^ 2 * ‖tail r g‖ := by
      simp [regulated, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hG]
    _ ≤ 1 * ‖tail r g‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hG.le hGOne) (norm_nonneg _)
    _ ≤ epsilon * g ^ N := by simpa using hTail

theorem pointwise_limit (g : ℝ) :
    Tendsto (fun r => regulated r g) (𝓝[>] 0) (𝓝 (continuum g)) := by
  have h : Tendsto (fun r : ℝ => -r / g) (𝓝[>] 0) (𝓝 0) := by
    have hId : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using hId.neg.div_const g
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp h
  have hComplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hExp
  simpa [regulated, continuum, tail] using
    (hComplex.const_mul ((g : ℂ) ^ 2)).const_add (1 : ℂ)

theorem coefficient_limit (k : ℕ) :
    Tendsto (fun _ : ℝ => coefficient k) (𝓝[>] 0) (𝓝 (coefficient k)) :=
  tendsto_const_nhds

theorem continuum_leading : Tendsto continuum (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun g : ℝ => (g : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  change Tendsto (fun g : ℝ => 1 + (g : ℂ) ^ 2) (𝓝[>] 0) (𝓝 1)
  simpa using (h.pow 2).const_add (1 : ℂ)

theorem continuum_not_prescribed_jet :
    ¬ YangMills.RG.HasPerturbativeJet continuum coefficient := by
  intro h
  obtain ⟨delta, hDelta, hBound⟩ := h 2 (1 / 2) (by norm_num)
  have hG : 0 < delta / 2 := by positivity
  have hGDelta : delta / 2 < delta := by linarith
  have hRem := hBound (delta / 2) hG hGDelta
  rw [partial_sum] at hRem
  have hNorm : ‖continuum (delta / 2) - 1‖ = (delta / 2) ^ 2 := by
    simp [continuum, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDelta]
  rw [hNorm] at hRem
  nlinarith [sq_pos_of_pos hG]

theorem no_uniform_order_two_remainder :
    ¬ (∃ delta : ℝ, 0 < delta ∧ ∀ g : ℝ, 0 < g → g < delta →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ‖regulated r g - ∑ k ∈ Finset.range (2 + 1),
          (g : ℂ) ^ k * coefficient k‖ ≤ (1 / 2) * g ^ 2) := by
  rintro ⟨delta, hDelta, hBound⟩
  have hG : 0 < delta / 2 := by positivity
  have hGDelta : delta / 2 < delta := by linarith
  have hLimit := ((pointwise_limit (delta / 2)).sub_const 1).norm
  have hRegulated := hBound (delta / 2) hG hGDelta
  simp only [partial_sum] at hRegulated
  have hRem := le_of_tendsto hLimit hRegulated
  have hNorm : ‖continuum (delta / 2) - 1‖ = (delta / 2) ^ 2 := by
    simp [continuum, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDelta]
  rw [hNorm] at hRem
  nlinarith [sq_pos_of_pos hG]

theorem regulated_smooth (r : ℝ) :
    ContDiffOn ℝ ⊤ (regulated r) (Set.Ioi 0) := by
  intro g hG
  have hNe : g ≠ 0 := ne_of_gt hG
  have hCast : ContDiffAt ℝ ⊤ (fun x : ℝ => (x : ℂ)) g :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hExp : ContDiffAt ℝ ⊤ (fun x : ℝ => Real.exp (-r / x)) g := by
    fun_prop (disch := assumption)
  exact (contDiffAt_const.add ((hCast.pow 2).mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp g hExp))).contDiffWithinAt

#print axioms partial_sum
#print axioms tail_ratio_limit
#print axioms tail_has_zero_jet
#print axioms fixed_regulator_jet
#print axioms pointwise_limit
#print axioms coefficient_limit
#print axioms continuum_leading
#print axioms continuum_not_prescribed_jet
#print axioms no_uniform_order_two_remainder
#print axioms regulated_smooth

end YMYMG.LimitAudit
