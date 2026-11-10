import ImportedAFSpecification
import YM.TraceExtension.Endpoint
import SourceScalar

set_option autoImplicit false
noncomputable section
namespace YMAFBridge
open YM YM.Table Filter Set
open scoped Topology

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- The endpoint's centering is exactly the field used in the completed OS bridge. -/
theorem same_center : TraceExtension.center F = Trace.traceField F := by
  rw [Trace.traceField_eq]
  have h : Trace.theta F 0 = TraceExtension.stressTrace F.sector.energy := by
    simp [Trace.theta, Trace.withoutMean, TraceExtension.stressTrace]
  rw [h]
  unfold TraceExtension.center TraceExtension.theta TraceExtension.centerIn
  congr 1
  rw [← Trace.mean_correct, Trace.onept_eq, h]
  rfl

/-- Same centered selected-phase kernel, with one insertion at the origin. -/
def K₂ (x : SpaceTime) : ℝ :=
  (YMOSBridge.scalarKernel F 2 (points ![x, 0])).re

theorem K₂_radial {x : SpaceTime} (hx : x ≠ 0) :
    K₂ F x = (TraceExtension.euclidean F ‖x‖).re := by
  have hc : points ![x, 0] ∈ conf 2 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [points]
  have h := Trace.Verse.axis_shape F (points ![x, 0]) hc
  have hw : Trace.Verse.width (points ![x, 0]) = ‖x‖ := by
    simp [Trace.Verse.width, points]
  rw [hw, same_center F] at h
  exact congrArg Complex.re h

theorem canonical_award (hG : G.Simple) :
    Trace.Verse.award G = 3 * (G.lieDim : ℝ) / Real.pi ^ 4 := by
  unfold Trace.Verse.award
  rw [Trace.Over.force_b]
  field_simp [(Gauge.casimir_pos hG).ne']
  ring

/-- Full punctured-space leading limit, not only a time-axis or sequence limit. -/
theorem leading_all_directions (hG : G.Simple) (h : Trace.Target.Result F hG) :
    Tendsto (fun x : SpaceTime => K₂ F x * ‖x‖ ^ 8 * uvLog 1 x ^ 2)
      (𝓝[≠] 0) (𝓝 (3 * (G.lieDim : ℝ) / Real.pi ^ 4)) := by
  have ht := (Complex.continuous_re.tendsto _).comp
    (h.shortDistance.comp (tendsto_norm_nhdsNE_zero (E := SpaceTime)))
  rw [canonical_award hG] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hn : x ≠ 0 := hx
  rw [K₂_radial F hn]
  simp only [Function.comp_apply, uvLog, one_mul, one_div, Complex.smul_re, smul_eq_mul]
  ring

/-- Exact leading predicate imported from the group's formulation. -/
theorem kernelUVPowerLaw (hG : G.Simple) (h : Trace.Target.Result F hG) :
    KernelUVPowerLaw (K₂ F) := by
  refine ⟨3 * (G.lieDim : ℝ) / Real.pi ^ 4, 1, ?_, by norm_num,
    leading_all_directions F hG h⟩
  rw [← canonical_award hG]
  exact h.positive

/-- The submitted existence theorem supplies the hypothesis used above. -/
theorem constructed_leading (G : Gauge) (hG : G.Simple)
    (p : Extraction.Order) :
    ∃ (C : Family G) (o : Extraction.Order) (S : Table C.book)
      (F : Spec.Final C o S), KernelUVPowerLaw (K₂ F) := by
  obtain ⟨C, _, _, _, _, q, ⟨S, ⟨F⟩⟩, hr⟩ :=
    Trace.Target.main.{0} G hG 1 (by norm_num) p
  exact ⟨C, p.refine q, S, F, kernelUVPowerLaw F hG (hr S F)⟩

end YMAFBridge
