import OutputRecoveryCoherent
import YangMills.GeneratedEuclideanCoefficients

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Construct a single distribution-valued outgoing coefficient table.
For equal-degree coordinate changes it satisfies the native locality,
graph-order, partial-scaling and all-cutoff recovery fields. The raw data
are retained: incoming extractor regularity and raw-limit transport are
not asserted, so no full GeneratedEuclideanData.Compatible is constructed. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.GeneratedOutputTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization YMYMG.OutputRecoveryCoherent

theorem local_sub_smul {n : ℕ} (U V : OPE.MultiDistribution n) (a : ℂ)
    (hU : OPE.IsLocalMultiDistribution U) (hV : OPE.IsLocalMultiDistribution V) :
    OPE.IsLocalMultiDistribution (U-a • V) := by
  intro K hK
  obtain ⟨N, b, hb, hu⟩ := hU K hK
  obtain ⟨M, d, hd, hv⟩ := hV K hK
  refine ⟨max N M, b+‖a‖*d, by positivity, ?_⟩
  intro f hf
  let σ (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), SchwartzMap.seminorm ℂ 0 j f
  have hσ (i j : ℕ) (hij : i ≤ j) : σ i ≤ σ j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hij 1))
    intro k _ _
    exact apply_nonneg _ _
  change ‖U f-a*V f‖ ≤ (b+‖a‖*d)*σ (max N M)
  calc
    _ ≤ ‖U f‖ + ‖a‖*‖V f‖ := by simpa only [norm_mul] using norm_sub_le (U f) (a*V f)
    _ ≤ b*σ N + ‖a‖*(d*σ M) := add_le_add (hu f hf)
      (mul_le_mul_of_nonneg_left (hv f hf) (norm_nonneg a))
    _ ≤ b*σ (max N M) + ‖a‖*(d*σ (max N M)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hσ N _ (le_max_left _ _)) hb)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hσ M _ (le_max_right _ _)) hd) (norm_nonneg a))
    _ = _ := by ring

theorem scaling_sub_smul {n : ℕ} (U V : OPE.MultiDistribution n) (a : ℂ)
    (input : Fin (n+1) → ℕ) (output : ℕ)
    (hU : OPE.PartialScalingBounds U input output)
    (hV : OPE.PartialScalingBounds V input output) :
    OPE.PartialScalingBounds (U-a • V) input output := by
  intro S f hf δ hδ
  have h := (hU S f hf δ hδ).sub ((hV S f hf δ hδ).const_mul a)
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    mul_sub, mul_left_comm, mul_zero, sub_zero] using! h

variable {G : CompactSimpleGaugeGroup} {basis : OPE.FilteredBasis G}

def changeOutputs (E : GeneratedEuclideanData basis) (high low : basis.Index)
    (a : ℝ) : GeneratedEuclideanData basis where
  raw := E.raw
  physical order loop n inputs last output := E.physical order loop n inputs last output -
    if output = low then (a : ℂ) •
      delay (fun r l => E.physical r l n inputs last high) order loop else 0

theorem raw_unchanged (E : GeneratedEuclideanData basis) (high low : basis.Index) (a : ℝ) :
    (changeOutputs E high low a).raw = E.raw := rfl

/-- Evaluation commutes with the one globally defined distribution-valued
coefficient correction; the result is not chosen afresh for each test. -/
theorem outputs_apply (E : GeneratedEuclideanData basis) (high low : basis.Index)
    (a : ℝ) (order loop n : ℕ) (inputs : Fin n → basis.Index) (last output : basis.Index)
    (f : OPE.RelativeTest n) :
    (changeOutputs E high low a).physical order loop n inputs last output f =
      coordinateCorrection high low a (fun r l i => E.physical r l n inputs last i f)
        order loop output := by
  have he := map_delay (fun T : OPE.MultiDistribution n => T f) (by simp)
    (fun r l => E.physical r l n inputs last high) order loop
  by_cases ho : output = low
  · simp only [changeOutputs, coordinateCorrection, if_pos ho,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, he]
  · simp [changeOutputs, coordinateCorrection, ho]

variable {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}
    {transport : SameTheoryWardTransportData e (S.insertions S.referenceScale.val)}

theorem outputs_graph (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (high low : basis.Index) (a : ℝ)
    (order loop n : ℕ) (inputs : Fin n → basis.Index) (last output : basis.Index)
    (horder : order < 2*loop) :
    (changeOutputs E high low a).physical order loop n inputs last output = 0 := by
  ext f
  rw [outputs_apply]
  exact coordinateCorrection_graph high low a _
    (fun r l i hr => by simp [h.physical_graph_order r l n inputs last i hr])
    order loop output horder

theorem outputs_local (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (high low : basis.Index) (a : ℝ)
    (order loop n : ℕ) (inputs : Fin n → basis.Index) (last output : basis.Index) :
    OPE.IsLocalMultiDistribution
      ((changeOutputs E high low a).physical order loop n inputs last output) := by
  by_cases ho : output = low
  · subst output
    obtain order | order | order := order <;> cases loop
    all_goals simp only [changeOutputs, ↓reduceIte, delay, smul_zero, sub_zero]
    all_goals first
      | exact h.physical_local _ _ n inputs last low
      | exact local_sub_smul _ _ _ (h.physical_local _ _ n inputs last low)
          (h.physical_local _ _ n inputs last high)
  · simpa only [changeOutputs, if_neg ho, sub_zero] using h.physical_local order loop n inputs last output

theorem outputs_scaling (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (high low : basis.Index)
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ)
    (order loop n : ℕ) (inputs : Fin n → basis.Index) (last output : basis.Index) :
    OPE.PartialScalingBounds
      ((changeOutputs E high low a).physical order loop n inputs last output)
      (clusterInputDegrees inputs last) (OPE.dimension (basis.label output)) := by
  have hhigh (r l : ℕ) : OPE.PartialScalingBounds
      (E.physical r l n inputs last high) (clusterInputDegrees inputs last)
      (OPE.dimension (basis.label low)) := by
    rw [hd]
    exact h.physical_power_counting r l n inputs last high
  by_cases ho : output = low
  · subst output
    cases loop with
    | zero =>
      simpa only [changeOutputs, ↓reduceIte, delay, smul_zero, sub_zero] using!
        h.physical_power_counting order 0 n inputs last low
    | succ loop =>
      obtain order | order | order := order
      · simpa only [changeOutputs, ↓reduceIte, delay, smul_zero, sub_zero] using!
          h.physical_power_counting 0 (loop+1) n inputs last low
      · simpa only [changeOutputs, ↓reduceIte, delay, smul_zero, sub_zero] using!
          h.physical_power_counting 1 (loop+1) n inputs last low
      · simpa only [changeOutputs, ↓reduceIte, delay] using!
          scaling_sub_smul _ _ (a : ℂ) (clusterInputDegrees inputs last)
            (OPE.dimension (basis.label low))
            (h.physical_power_counting (order+2) (loop+1) n inputs last low) (hhigh order loop)
  · simpa only [changeOutputs, if_neg ho, sub_zero] using
      h.physical_power_counting order loop n inputs last output

/-- The literal native physical_recovery field, for the new shared output
table and unchanged raw vector. This does not assert the new raw_limit or
regularity fields, because the incoming extractor also changes. -/
theorem outputs_recovery (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (high low : basis.Index)
    (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ)
    (n : ℕ) (inputs : Fin n → basis.Index) (last : basis.Index) (cutoff : ℕ)
    (f : OPE.RelativeTest n) (hf : OPE.MultiOffDiagonal f) :
    ∃ count : ℕ, ∃ index : Fin count → basis.Index,
      Function.Injective index ∧ Finset.univ.image index = basis.active cutoff ∧
      QuantumPhysicalOutputRecovery e (S.insertions S.referenceScale.val) transport
        (change lift (coordinateDirectionLE basis high low hpos hd.le) a) W Q cutoff
        (fun i => basis.label (index i))
        (fun r l m => (changeOutputs E high low a).raw r l n inputs last m f)
        (fun r l i => (changeOutputs E high low a).physical r l n inputs last (index i) f) := by
  have hold : CoherentRecovery basis e (S.insertions S.referenceScale.val) transport lift W Q
      (fun r l m => E.raw r l n inputs last m f)
      (fun r l i => E.physical r l n inputs last i f) :=
    fun d => h.physical_recovery n inputs last d f hf
  have hnew := coherent_coordinate_change basis high low hne hpos hd a _ _ hold cutoff
  simpa only [raw_unchanged, outputs_apply] using! hnew

#print axioms local_sub_smul
#print axioms scaling_sub_smul
#print axioms raw_unchanged
#print axioms outputs_apply
#print axioms outputs_graph
#print axioms outputs_local
#print axioms outputs_scaling
#print axioms outputs_recovery
end YMYMG.GeneratedOutputTransport
