import GeneratedDataTransport
import ScaleNormalizationTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Assemble generated coefficient transport at every subtraction scale
with the already constructed Ward family and scale normalization. -/
noncomputable section
open scoped ContDiff
namespace YMYMG.GeneratedDataTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow YangMills.ScaleInsertion
open YMYMG.DictionaryRenormalization YMYMG.OutputRecoveryCoherent
open YMYMG.ScaleNormalizationTransport

variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} {basis : OPE.FilteredBasis G}

theorem coordinate_lower_weight_zero (high low : basis.Index) (hne : high ≠ low)
    (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) :
    (coordinateDirectionLE basis high low hpos hd.le).weight
      (coordinateDirectionLE basis high low hpos hd.le).lower = 0 := by
  change (coordinateDirectionLE basis high low hpos hd.le).weight (basis.label low) = 0
  rw [directionLE_weights]
  exact if_neg (Ne.symm hne)

/-- The coefficient family is one scale-indexed collection of actual
distributions, with the entire native compatibility proof at every scale. -/
def changeCoefficientFamily (family : LocalWardFlowFamily S)
    (E : LocalWardCoefficientFamily family basis) (high low : basis.Index)
    (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : RenormalizationScale → ℝ) :
    LocalWardCoefficientFamily
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a) basis where
  data mu := changeGenerated (E.data mu) high low (a mu)
  compatible mu := compatible_change (E.data mu) (E.compatible mu) high low hne hpos hd (a mu)

theorem coefficientFamily_exists_iff (family : LocalWardFlowFamily S)
    (high low : basis.Index) (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : RenormalizationScale → ℝ) :
    Nonempty (LocalWardCoefficientFamily
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a) basis) ↔
    Nonempty (LocalWardCoefficientFamily family basis) := by
  constructor
  · rintro ⟨E⟩
    have back := changeCoefficientFamily
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a) E
      high low hne hpos hd (fun mu => -a mu)
    rw [changeFamily_inverse family _ a (coordinate_lower_weight_zero high low hne hpos hd)] at back
    exact ⟨back⟩
  · rintro ⟨E⟩
    exact ⟨changeCoefficientFamily family E high low hne hpos hd a⟩

def changeNormalizedData (family : LocalWardFlowFamily S)
    (E : LocalWardCoefficientFamily family basis) (N : GeneratedScaleNormalization family)
    (high low : basis.Index) (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0)) :
    LocalWardCoefficientFamily
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a) basis ×
    GeneratedScaleNormalization
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a) :=
  ⟨changeCoefficientFamily family E high low hne hpos hd a,
    changeNormalization family N (coordinateDirectionLE basis high low hpos hd.le)
      (coordinate_lower_weight_zero high low hne hpos hd) a ha⟩

/-- These native coefficient and normalization witnesses can be supplied
together in either presentation. Physical reconstruction and asymptotic
matching are not asserted by this equivalence. -/
theorem normalizedData_exists_iff (family : LocalWardFlowFamily S)
    (high low : basis.Index) (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0)) :
    (Nonempty (LocalWardCoefficientFamily
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a) basis) ∧
     Nonempty (GeneratedScaleNormalization
      (changeFamily family (coordinateDirectionLE basis high low hpos hd.le) a))) ↔
    (Nonempty (LocalWardCoefficientFamily family basis) ∧ Nonempty (GeneratedScaleNormalization family)) :=
  and_congr (coefficientFamily_exists_iff family high low hne hpos hd a)
    (normalization_exists_iff family (coordinateDirectionLE basis high low hpos hd.le)
      (coordinate_lower_weight_zero high low hne hpos hd) a ha)

#print axioms coordinate_lower_weight_zero
#print axioms changeCoefficientFamily
#print axioms coefficientFamily_exists_iff
#print axioms changeNormalizedData
#print axioms normalizedData_exists_iff
end YMYMG.GeneratedDataTransport
