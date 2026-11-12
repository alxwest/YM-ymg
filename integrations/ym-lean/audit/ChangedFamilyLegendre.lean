import PhysicalWordTransport
import YangMills.GeneratedScaleNormalization
import YangMills.LegendreFlowAdapters

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Two scale-insertion obligations follow from the unchanged fixed flow.
This file does not construct new mixing, primitives, smoothness or a CS
residual limit. It assumes the original scale normalization exists. -/
noncomputable section
namespace YMYMG.DictionaryRenormalization
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.LegendreInsertionBridge
variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
  {S : FixedFlowSystem e} {family : LocalWardFlowFamily S}

/-- The precise lifted-directional field of CompositeCSConditions for
the changed family, using the existing same-background Legendre equation. -/
theorem changeFamily_lift_directional (N : GeneratedScaleNormalization family)
    (D : Direction G) (a : RenormalizationScale → ℝ)
    (mu : ℝ) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime)
    (hmu : 0 < mu) (hs : mu < s.ultraviolet) :
    DirectionalLegendreCompatible (S.background mu)
      (fun g => (positiveScaleExtension S.referenceScale
        (changeFamily family D a).lift mu).finiteInsertion
          (S.insertions mu g) g p x) s :=
  fixedFlow_lift_directional_of_legendre S mu hmu s
    (N.same_scale_insertion.action.legendre mu s hmu hs) _ p x

/-- The exact-directional field also holds for any proposed admissible
primitive family. Choosing primitives that solve the changed CS equation
is a separate obligation. The anomaly and insertion flows are unchanged. -/
theorem changeFamily_exact_directional (N : GeneratedScaleNormalization family)
    (D : Direction G) (a : RenormalizationScale → ℝ)
    (primitive : (p : InvariantInsertionLabel G) →
      LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (mu : ℝ) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime)
    (hmu : 0 < mu) (hs : mu < s.ultraviolet) :
    DirectionalLegendreCompatible (S.background mu)
      (fun g => quantumExactInsertion e
        (positiveScaleExtension S.referenceScale
          (fun scale => ((changeFamily family D a).singleTransport scale).coefficient))
        S.insertions (primitive p) mu g x) s :=
  fixedFlow_exact_directional_of_legendre S mu hmu s
    (N.same_scale_insertion.action.legendre mu s hmu hs) _ (primitive p) x

#print axioms changeFamily_lift_directional
#print axioms changeFamily_exact_directional
end YMYMG.DictionaryRenormalization
