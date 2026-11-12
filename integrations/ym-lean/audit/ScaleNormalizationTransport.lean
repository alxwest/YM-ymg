import ExactLegendreTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Transport of a complete existing native scale normalization.
The primitive and mixing are constructed, the actual residual is transported,
and its UV-then-IR limit follows from the original equations. No original
interacting family, reconstruction or existence certificate is constructed. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace YMYMG.ScaleNormalizationTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre
open YMYMG.DictionaryRenormalization YMYMG.LegendreTransport YMYMG.ScaleTransport
open YMYMG.MixingTransport YMYMG.ExactTransport
variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
  {S : FixedFlowSystem e}

theorem family_residual_change (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G) (hq : D.weight D.lower = 0)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0))
    (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (hs : mu < s.ultraviolet)
    (p : InvariantInsertionLabel G) (x : Spacetime) :
    let ae := positiveScaleExtension S.referenceScale a
    let anomaly := positiveScaleExtension S.referenceScale
      (fun scale => (family.singleTransport scale).coefficient)
    let old := fun label => compositeResidual e anomaly S.background S.insertions
      (positiveScaleExtension S.referenceScale family.lift) N.beta N.fields N.mixing N.primitive
      mu s label x
    compositeResidual e anomaly S.background S.insertions
      (positiveScaleExtension S.referenceScale (changeFamily family D a).lift)
      N.beta N.fields (changeMixing N.mixing D hq N.beta ae ha)
      (changePrimitive N.primitive D ae ha) mu s p x =
      old p + ((ae mu*D.weight p : ℝ) : ℂ) • amplitudeDelay (old D.lower) := by
  dsimp only
  simp only [compositeResidual_parts]
  rw [family_differential_mixing_change family N D hq a ha mu hmu s hs p x,
    family_exactGamma_change family N.primitive D _ ha mu hmu s p x,
    amplitudeDelay_sub]
  funext r l legs q
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem family_residual_weak (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G) (hq : D.weight D.lower = 0)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0))
    (mu : ℝ) (p : InvariantInsertionLabel G) (hmu : 0 < mu) :
    let ae := positiveScaleExtension S.referenceScale a
    let anomaly := positiveScaleExtension S.referenceScale
      (fun scale => (family.singleTransport scale).coefficient)
    WeakLocalEndpointZero (fun IR UV x => if h : 0 < IR ∧ IR ≤ UV then
      compositeResidual e anomaly S.background S.insertions
        (positiveScaleExtension S.referenceScale (changeFamily family D a).lift)
        N.beta N.fields (changeMixing N.mixing D hq N.beta ae ha)
        (changePrimitive N.primitive D ae ha) mu ⟨IR,UV,h.1,h.2⟩ p x else 0) := by
  dsimp only
  apply weakLocal_congr_eventually
    (weakLocal_add (N.same_scale_insertion.equation mu p hmu)
      (weakLocal_smul (((positiveScaleExtension S.referenceScale a mu)*D.weight p : ℝ) : ℂ)
        (weakLocal_delay (N.same_scale_insertion.equation mu D.lower hmu))))
  intro IR hIR
  filter_upwards [eventually_ge_atTop IR, eventually_gt_atTop mu] with UV hUV hs
  funext x
  simp only [dif_pos (show 0 < IR ∧ IR ≤ UV from ⟨hIR,hUV⟩)]
  exact (family_residual_change family N D hq a ha mu hmu ⟨IR,UV,hIR,hUV⟩ hs p x).symm

/-- Every field of GeneratedScaleNormalization is filled with native data.
The original normalized family remains a hypothesis. -/
def changeNormalization (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G) (hq : D.weight D.lower = 0)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0)) :
    GeneratedScaleNormalization (changeFamily family D a) where
  beta := N.beta
  fields := N.fields
  actionPrimitive := N.actionPrimitive
  mixing := changeMixing N.mixing D hq N.beta (positiveScaleExtension S.referenceScale a) ha
  primitive := changePrimitive N.primitive D (positiveScaleExtension S.referenceScale a) ha
  beta_graph_order := N.beta_graph_order
  fields_graph_order := N.fields_graph_order
  mixing_graph_order := changeMixing_graph N.mixing D hq N.beta _ ha
    N.mixing_graph_order N.beta_graph_order
  same_scale_insertion := {
    action := N.same_scale_insertion.action
    same_dictionary := by
      intro mu hmu
      rw [positiveScale_change]
      exact compatible (N.same_scale_insertion.same_dictionary mu hmu) D _
    lifted_scale_smooth := changeFamily_scale_smooth family N D a ha
    lifted_directional := changeFamily_lift_directional N D a
    exact_directional := changeFamily_exact_directional N D a _
    equation := family_residual_weak family N D hq a ha
  }

theorem positiveScale_neg (a : RenormalizationScale → ℝ) (mu : ℝ) :
    positiveScaleExtension S.referenceScale (fun scale => -a scale) mu =
      -positiveScaleExtension S.referenceScale a mu := by
  classical
  by_cases hm : 0 < mu <;> simp [positiveScaleExtension, hm]

/-- Equivalence of existence of a normalization for the two presentations.
It does not assert equality of the freely represented mixing tables after
round-trip transport, or equivalence of the complete existence targets. -/
theorem normalization_exists_iff (family : LocalWardFlowFamily S)
    (D : Direction G) (hq : D.weight D.lower = 0) (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0)) :
    Nonempty (GeneratedScaleNormalization (changeFamily family D a)) ↔
      Nonempty (GeneratedScaleNormalization family) := by
  constructor
  · rintro ⟨N⟩
    have hn : ContDiffOn ℝ ∞
        (positiveScaleExtension S.referenceScale (fun scale => -a scale)) (Set.Ioi 0) := by
      rw [show positiveScaleExtension S.referenceScale (fun scale => -a scale) =
        (fun mu => -positiveScaleExtension S.referenceScale a mu) from
          funext (positiveScale_neg (S := S) a)]
      exact ha.neg
    have NN := changeNormalization (changeFamily family D a) N D hq (fun scale => -a scale) hn
    rw [changeFamily_inverse family D a hq] at NN
    exact ⟨NN⟩
  · rintro ⟨N⟩
    exact ⟨changeNormalization family N D hq a ha⟩

#print axioms family_residual_change
#print axioms family_residual_weak
#print axioms changeNormalization
#print axioms positiveScale_neg
#print axioms normalization_exists_iff
end YMYMG.ScaleNormalizationTransport
