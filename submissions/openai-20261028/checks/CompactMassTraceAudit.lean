import CompactMassTrace

/-!
# Compact-mass trace check for the countermodel in ym-lean issue #5

The test uses normalized Lebesgue measure on the mass-squared interval
`[1, 4]`. The square root pushes it to the mass interval `[1, 2]`.
-/

set_option autoImplicit false

noncomputable section

namespace YMReview.CompactMassTrace

open Filter MeasureTheory Set YM.TraceExtension.Wick
open scoped ENNReal Topology

private abbrev MassSquared := Icc (1 : ℝ) 4

private def massSquaredMeasure : Measure MassSquared :=
  (3 : ℝ≥0∞)⁻¹ • Measure.comap (Subtype.val : MassSquared → ℝ) volume

private lemma massSquaredMeasure_univ : massSquaredMeasure univ = 1 := by
  rw [massSquaredMeasure, Measure.smul_apply, smul_eq_mul,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply, image_univ,
    Subtype.range_coe_subtype]
  change (3 : ℝ≥0∞)⁻¹ * volume (Icc (1 : ℝ) 4) = 1
  rw [Real.volume_Icc]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

private def massFromSquare (s : MassSquared) : Icc (1 : ℝ) 2 :=
  ⟨Real.sqrt (s : ℝ), by
    constructor
    · simpa using Real.sqrt_le_sqrt s.property.1
    · have h := Real.sqrt_le_sqrt s.property.2
      rwa [show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]] at h⟩

private lemma massFromSquare_measurable : Measurable massFromSquare :=
  ((Real.continuous_sqrt.comp continuous_subtype_val).subtype_mk
    (fun s => (massFromSquare s).property)).measurable

private lemma massFromSquare_injective : Function.Injective massFromSquare := by
  intro x y h
  apply Subtype.ext
  have he : Real.sqrt (x : ℝ) = Real.sqrt (y : ℝ) := congrArg Subtype.val h
  have hx : 0 ≤ (x : ℝ) := zero_le_one.trans x.property.1
  have hy : 0 ≤ (y : ℝ) := zero_le_one.trans y.property.1
  have hsq : Real.sqrt (x : ℝ) ^ 2 = Real.sqrt (y : ℝ) ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) he
  rwa [Real.sq_sqrt hx, Real.sq_sqrt hy] at hsq

/-- Normalized Lebesgue mass-squared measure, pushed forward by square root. -/
def uniformMassSquared : CompactMassMeasure where
  lower := 1
  upper := 2
  lower_pos := zero_lt_one
  measure := Measure.map massFromSquare massSquaredMeasure
  finite := by
    letI : IsProbabilityMeasure massSquaredMeasure := ⟨massSquaredMeasure_univ⟩
    exact Measure.isFiniteMeasure_map massSquaredMeasure massFromSquare

theorem uniformMassSquared_probability : uniformMassSquared.measure univ = 1 := by
  change Measure.map massFromSquare massSquaredMeasure univ = 1
  rw [Measure.map_apply massFromSquare_measurable MeasurableSet.univ, preimage_univ,
    massSquaredMeasure_univ]

theorem uniformMassSquared_singleton (m : Icc (1 : ℝ) 2) :
    uniformMassSquared.measure {m} = 0 := by
  change Measure.map massFromSquare massSquaredMeasure {m} = 0
  rw [Measure.map_apply massFromSquare_measurable (measurableSet_singleton m),
    massSquaredMeasure, Measure.smul_apply,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  have h := ((subsingleton_singleton (a := m)).preimage massFromSquare_injective).image
    (Subtype.val : MassSquared → ℝ)
  rw [h.measure_zero volume, smul_zero]

private def scalarShell : YangMills.Hierarchy.Mode where
  mass := 1
  spatialOrder := 0
  timeOrder := 0
  numerator := fun _ => 1
  continuous := continuous_const
  homogeneous := by simp

private def scalarMode : AveragedMode := AveragedMode.ofShell uniformMassSquared scalarShell

/-- The centered two-point profile of the scalar Wick square. -/
def uniformMassSquaredWickSquare (r : ℝ) : ℂ :=
  ((2 : ℝ) * (scalarMode.eval r) ^ 2 : ℝ)

theorem excludes_uniformMassSquaredWickSquare {g : YangMills.GaugeGroup}
    {C : YangMills.WilsonFamily g} {T : YangMills.Hierarchy C} (h : T.TraceTest) :
    ¬ T.traceTwo =ᶠ[past] uniformMassSquaredWickSquare := by
  intro heq
  apply excludes h [(2, [scalarMode, scalarMode])]
  filter_upwards [heq] with r hr
  rw [hr]
  simp [uniformMassSquaredWickSquare, wickProfile, pow_two]

end YMReview.CompactMassTrace

#print axioms YMReview.CompactMassTrace.AveragedMode.ofShell_eval
#print axioms YMReview.CompactMassTrace.excludes
#print axioms YMReview.CompactMassTrace.uniformMassSquared_probability
#print axioms YMReview.CompactMassTrace.uniformMassSquared_singleton
#print axioms YMReview.CompactMassTrace.excludes_uniformMassSquaredWickSquare
