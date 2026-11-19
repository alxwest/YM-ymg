import ChallengeSpec
import YM.TraceExtension.Wick.Log
import YM.TraceExtension.Wick.PolynomialField

/-!
# Compact mass distributions in the centered trace test

The moment expansion at mass one controls every mass in a compact positive
interval by dilation. Averaging those expansions extends the October trace
test to finite Wick profiles with such mass distributions.
-/

set_option autoImplicit false

noncomputable section

namespace YMReview.CompactMassTrace

open Asymptotics Filter MeasureTheory Set YM.TraceExtension.Wick
open scoped Topology

/-- A finite spectral measure on a compact interval of strictly positive masses. -/
structure CompactMassMeasure where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  measure : Measure (Icc lower upper)
  finite : IsFiniteMeasure measure

namespace CompactMassMeasure

abbrev Mass (μ : CompactMassMeasure) := Icc μ.lower μ.upper

private lemma mass_pos (μ : CompactMassMeasure) (m : μ.Mass) : 0 < (m : ℝ) :=
  μ.lower_pos.trans_le m.property.1

/-- The integral of the source's radial moment against the mass distribution. -/
def momentAverage (μ : CompactMassMeasure) (j k : ℕ) (r : ℝ) : ℝ :=
  ∫ m : μ.Mass, moment (m : ℝ) j k r ∂μ.measure

private def dilatedAverage (μ : CompactMassMeasure) (power : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ m : μ.Mass, (m : ℝ) ^ power * f ((m : ℝ) * r) ∂μ.measure

theorem moment_rescale {m : ℝ} (hm : 0 < m) (j k : ℕ) (r : ℝ) :
    moment m j k r = m ^ (j + k + 2) * moment 1 j k (m * r) := by
  have freq_rescale (t : ℝ) : freq m (m * t) = m * freq 1 t := by
    calc
      freq m (m * t) = Real.sqrt (m ^ 2 * (1 ^ 2 + t ^ 2)) := by
        unfold freq
        congr 1
        ring
      _ = m * freq 1 t := by rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hm.le, freq]
  have stream_rescale (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      m * stream m j k r (m * t) = m ^ (j + k + 2) * stream 1 j k (m * r) t := by
    unfold stream
    rw [freq_rescale, mul_pow, mul_pow, show -r * (m * freq 1 t) = -(m * r) * freq 1 t by ring,
      show j + k + 2 = (j + 2) + k by omega, pow_add m (j + 2) k]
    field_simp [hm.ne', (freq_pos 1 ht).ne']
  unfold moment
  calc
    (∫ t in Ioi 0, stream m j k r t) = ∫ t in Ioi 0, m * stream m j k r (m * t) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 hm, mul_zero, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    _ = ∫ t in Ioi 0, m ^ (j + k + 2) * stream 1 j k (m * r) t :=
      setIntegral_congr_fun measurableSet_Ioi stream_rescale
    _ = m ^ (j + k + 2) * ∫ t in Ioi 0, stream 1 j k (m * r) t := integral_const_mul _ _

private lemma integrable_continuous (μ : CompactMassMeasure) {f : μ.Mass → ℝ}
    (hf : Continuous f) : Integrable f μ.measure := by
  letI := μ.finite
  letI : CompactSpace μ.Mass := isCompact_iff_compactSpace.mp isCompact_Icc
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private lemma integrable_dilation (μ : CompactMassMeasure) (power : ℕ) {f : ℝ → ℝ}
    {r : ℝ} (hr : 0 < r) (hf : ContinuousOn f (Ioi 0)) :
    Integrable (fun m : μ.Mass => (m : ℝ) ^ power * f ((m : ℝ) * r)) μ.measure := by
  apply μ.integrable_continuous
  exact (continuous_subtype_val.pow power).mul
    (hf.comp_continuous (continuous_subtype_val.mul continuous_const)
      (fun m => mul_pos (μ.mass_pos m) hr))

private lemma continuousOn_board {f : ℝ → ℝ} (hf : f ∈ board) : ContinuousOn f (Ioi 0) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨a, k, rfl⟩ := hf
      have hfill : ContinuousOn fill (Ioi 0) :=
        continuous_id.continuousOn.congr (fun _ hr => fill_at hr)
      exact (hfill.zpow₀ a (fun r _ => Or.inl (fill_away r))).mul
        ((Real.continuousOn_log.comp hfill (fun r _ => fill_away r)).pow k)
  | zero => exact continuous_const.continuousOn
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

/-- Dilation shifts each logarithm by a mass-dependent constant. The average
of every term in the expansion is again a finite power-log expression. -/
private lemma dilatedAverage_board (μ : CompactMassMeasure) (power : ℕ)
    {f : ℝ → ℝ} (hf : f ∈ board) :
    ∃ g ∈ board, ∀ r > 0, μ.dilatedAverage power f r = g r := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨a, k, rfl⟩ := hf
      let coeff (i : ℕ) (m : μ.Mass) : ℝ :=
        (m : ℝ) ^ power * (m : ℝ) ^ a * (Real.log (m : ℝ)) ^ (k - i) * (k.choose i : ℝ)
      have hlog : Continuous (fun m : μ.Mass => Real.log (m : ℝ)) :=
        Real.continuousOn_log.comp_continuous continuous_subtype_val (fun m => (μ.mass_pos m).ne')
      have hc (i : ℕ) : Continuous (coeff i) :=
        (((continuous_subtype_val.pow power).mul
          (continuous_subtype_val.zpow₀ a (fun m => Or.inl (μ.mass_pos m).ne'))).mul
          (hlog.pow (k - i))).mul continuous_const
      refine ⟨∑ i ∈ Finset.range (k + 1), (∫ m, coeff i m ∂μ.measure) • joint a i,
        Submodule.sum_mem _ (fun i _ => board.smul_mem _ (jointBoard a i)), ?_⟩
      intro r hr
      calc
        μ.dilatedAverage power (joint a k) r =
            ∫ m, ∑ i ∈ Finset.range (k + 1), coeff i m * joint a i r ∂μ.measure := by
          apply integral_congr_ae
          exact ae_of_all _ fun m => by
            have hm := μ.mass_pos m
            simp only [joint, tile, fill_at hr, fill_at (mul_pos hm hr), mul_zpow,
              Real.log_mul hm.ne' hr.ne']
            rw [add_comm (Real.log (m : ℝ)) (Real.log r), add_pow]
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            dsimp [coeff]
            ring
        _ = _ := by
          rw [integral_finsetSum _ (fun i _ => (μ.integrable_continuous (hc i)).mul_const _)]
          simp only [integral_mul_const, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  | zero =>
      refine ⟨0, board.zero_mem, fun r _ => ?_⟩
      simp [dilatedAverage]
  | add f g hf hg ihf ihg =>
      obtain ⟨u, hu, huv⟩ := ihf
      obtain ⟨v, hv, hvv⟩ := ihg
      refine ⟨u + v, board.add_mem hu hv, fun r hr => ?_⟩
      simp only [dilatedAverage, Pi.add_apply, mul_add] at huv hvv ⊢
      rw [integral_add (μ.integrable_dilation power hr (continuousOn_board hf))
        (μ.integrable_dilation power hr (continuousOn_board hg)), huv r hr, hvv r hr]
  | smul c f _ ih =>
      obtain ⟨u, hu, huv⟩ := ih
      refine ⟨c • u, board.smul_mem c hu, fun r hr => ?_⟩
      simp only [dilatedAverage, Pi.smul_apply, smul_eq_mul] at huv ⊢
      simp_rw [mul_left_comm _ c, integral_const_mul, huv r hr]

private theorem dilatedAverage_expands (μ : CompactMassMeasure) (power : ℕ)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) (he : Expands f) :
    Expands (μ.dilatedAverage power f) := by
  intro n
  obtain ⟨q, hq, error⟩ := he n
  obtain ⟨v, hv, heq⟩ := μ.dilatedAverage_board power hq
  obtain ⟨C, _, hC⟩ := error.exists_pos
  obtain ⟨δ, hδ, herror⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hC.bound
  let upper := max 1 μ.upper
  have hupper : 0 < upper := zero_lt_one.trans_le (le_max_left _ _)
  have hcontinuous : ContinuousOn (fun m : ℝ => m ^ power * m ^ n) (Icc μ.lower μ.upper) :=
    (continuous_pow power).continuousOn.mul
      (continuous_id.continuousOn.zpow₀ n (fun m hm => Or.inl (μ.mass_pos ⟨m, hm⟩).ne'))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontinuous
  letI := μ.finite
  refine ⟨v, hv, isBigO_iff.mpr ⟨C * B * μ.measure.real univ, ?_⟩⟩
  filter_upwards [mostly_lt (div_pos hδ hupper)] with r hr
  rw [Pi.sub_apply, ← heq r hr.1]
  simp only [dilatedAverage, ← integral_sub (μ.integrable_dilation power hr.1 hf)
    (μ.integrable_dilation power hr.1 (continuousOn_board hq)), ← mul_sub]
  refine (norm_integral_le_of_norm_le_const (C := C * B * ‖tile n r‖) (ae_of_all _ ?_)).trans_eq
    (by ring)
  intro m
  have hm := μ.mass_pos m
  have hmr : (m : ℝ) * r ∈ Ioo 0 δ := ⟨mul_pos hm hr.1, calc
    (m : ℝ) * r ≤ upper * r := mul_le_mul_of_nonneg_right
      (m.property.2.trans (le_max_right _ _)) hr.1.le
    _ < δ := by simpa only [mul_comm upper r] using (lt_div_iff₀ hupper).mp hr.2⟩
  have hpoint := herror hmr
  change ‖f ((m : ℝ) * r) - q ((m : ℝ) * r)‖ ≤ C * ‖tile n ((m : ℝ) * r)‖ at hpoint
  rw [norm_mul]
  calc
    _ ≤ ‖(m : ℝ) ^ power‖ * (C * ‖tile n ((m : ℝ) * r)‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg _)
    _ = C * ‖(m : ℝ) ^ power * (m : ℝ) ^ n‖ * ‖tile n r‖ := by
      rw [tile, fill_at hmr.1, mul_zpow, norm_mul, norm_mul, tile, fill_at hr.1]
      ring
    _ ≤ _ := by
      gcongr
      exact hB (m : ℝ) m.property

/-- Uniform dilation followed by a finite mass integral retains the
source's expansion at every integer order. -/
theorem momentAverage_expands (μ : CompactMassMeasure) (j k : ℕ) :
    Expands (μ.momentAverage j k) := by
  have hscale : μ.momentAverage j k = μ.dilatedAverage (j + k + 2) (moment 1 j k) := by
    funext r
    apply integral_congr_ae
    exact ae_of_all _ fun m => moment_rescale (μ.mass_pos m) j k r
  rw [hscale]
  refine μ.dilatedAverage_expands _ (fun r hr => ?_) (moment_expands 1 j k)
  exact (moment_d 1 j k r hr).continuousAt.continuousWithinAt

end CompactMassMeasure

/-- Angular integration leaves only a coefficient and the two derivative
orders of each averaged mass-shell kernel. -/
structure AveragedMode where
  spectrum : CompactMassMeasure
  spatialOrder : ℕ
  timeOrder : ℕ
  angularFactor : ℝ

def AveragedMode.eval (mode : AveragedMode) (r : ℝ) : ℝ :=
  mode.angularFactor * mode.spectrum.momentAverage mode.spatialOrder mode.timeOrder r

/-- Replace the fixed mass in a public October mode by a spectral measure. -/
def AveragedMode.ofShell (spectrum : CompactMassMeasure) (mode : YangMills.Hierarchy.Mode) :
    AveragedMode :=
  let shell : YM.TraceExtension.Wick.Mode :=
    ⟨mode.mass, mode.spatialOrder, mode.timeOrder, mode.numerator, mode.continuous,
      fun p r hr => mode.homogeneous p r hr⟩
  ⟨spectrum, shell.j, shell.k, shell.angular * (2 : ℝ)⁻¹⟩

theorem AveragedMode.ofShell_eval (spectrum : CompactMassMeasure) (mode : YangMills.Hierarchy.Mode)
    (r : ℝ) :
    (ofShell spectrum mode).eval r =
      ∫ m : spectrum.Mass, (∫ p : YangMills.Space,
        ({mode with mass := ⟨(m : ℝ), (spectrum.mass_pos m).le⟩}).kernel r p) ∂spectrum.measure := by
  unfold ofShell eval CompactMassMeasure.momentAverage
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun m =>
    (YM.TraceExtension.Wick.Mode.field_value
      ⟨⟨(m : ℝ), (spectrum.mass_pos m).le⟩, mode.spatialOrder, mode.timeOrder, mode.numerator,
        mode.continuous, fun p r hr => mode.homogeneous p r hr⟩ r).symm

/-- Each Wick contraction is a finite product of averaged modes. The complex
coefficients collect the field coefficients and pairing multiplicities. -/
def wickProfile (terms : List (ℂ × List AveragedMode)) (r : ℝ) : ℂ :=
  (terms.map (fun (coefficient, modes) => coefficient * ((modes.map (fun m => m.eval r)).prod : ℝ))).sum

private lemma modes_expand (modes : List AveragedMode) :
    Expands (fun r => (modes.map (fun m => m.eval r)).prod) := by
  induction modes with
  | nil => exact own one_board
  | cons mode modes ih =>
      exact ((mode.spectrum.momentAverage_expands mode.spatialOrder mode.timeOrder).scale
        mode.angularFactor).mult ih

theorem wickProfile_expands (terms : List (ℂ × List AveragedMode)) :
    Expands (fun r => (wickProfile terms r).re) := by
  induction terms with
  | nil => exact own board.zero_mem
  | cons term terms ih =>
      convert ((modes_expand term.2).scale term.1.re).plus ih using 1
      funext r
      simp only [wickProfile, List.map_cons, List.sum_cons, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]

/-- The selected centered trace cannot agree near zero with any finite
Wick profile whose individual mass distributions have compact positive support. -/
theorem excludes {g : YangMills.GaugeGroup} {C : YangMills.WilsonFamily g}
    {T : YangMills.Hierarchy C} (h : T.TraceTest) (terms : List (ℂ × List AveragedMode)) :
    ¬ T.traceTwo =ᶠ[past] wickProfile terms := by
  intro heq
  have ht := (Complex.continuous_re.tendsto _).comp h.shortDistance
  have hLimit : Tendsto (fun r => r ^ 8 * (Real.log r⁻¹) ^ 2 * (wickProfile terms r).re) past
      (𝓝 (3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4)) := by
    apply ht.congr'
    filter_upwards [heq] with r hr
    simp only [Function.comp_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hr]
  exact h.amplitudePositive.ne' (no_powerlog (wickProfile_expands terms 0) hLimit)

end YMReview.CompactMassTrace
