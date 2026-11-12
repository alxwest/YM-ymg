import YangMills.GeneratedScaleNormalization

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
Reduction of the actual generated series, using its CS and graph-order
conditions. No conventional beta polynomial or freely chosen mixing table
is substituted for the same-flow coefficients.
-/
noncomputable section
open scoped BigOperators
namespace YMYMG.GeneratedAudit
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow

variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
  {S : FixedFlowSystem e} {family : LocalWardFlowFamily S}

theorem beta_below_three (N : GeneratedScaleNormalization family)
    (order : ℕ) (h : order < 3) : N.betaSeries order = 0 := by
  simp [GeneratedScaleNormalization.betaSeries,
    N.same_scale_insertion.action.beta_free, h]

theorem beta_three (N : GeneratedScaleNormalization family) :
    N.betaSeries 3 = N.beta 3 1 := by
  have h0 := N.same_scale_insertion.action.beta_classical 3
  have h2 := N.beta_graph_order 3 2 (by omega)
  have h3 := N.beta_graph_order 3 3 (by omega)
  simp [GeneratedScaleNormalization.betaSeries, Finset.sum_range_succ, h0, h2, h3]

theorem gamma_classical (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale) (order : ℕ)
    (output input : basis.Index) :
    N.euclideanGammaLoop basis mu order 0 output input = 0 := by
  simp [GeneratedScaleNormalization.euclideanGammaLoop,
    N.mixing.classical mu order (basis.label input) mu.property]

theorem gamma_below_two (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale) (order : ℕ)
    (h : order < 2) (output input : basis.Index) :
    N.euclideanGammaSeries basis mu order output input = 0 := by
  have ho : order / 2 = 0 := by omega
  simp [GeneratedScaleNormalization.euclideanGammaSeries, ho, gamma_classical]

theorem gamma_two (N : GeneratedScaleNormalization family)
    (basis : OPE.FilteredBasis G) (mu : RenormalizationScale)
    (output input : basis.Index) :
    N.euclideanGammaSeries basis mu 2 output input =
      (N.euclideanGammaLoop basis mu 2 1 output input : ℂ) := by
  simp [GeneratedScaleNormalization.euclideanGammaSeries,
    Finset.sum_range_succ, gamma_classical]

#print axioms beta_below_three
#print axioms beta_three
#print axioms gamma_classical
#print axioms gamma_below_two
#print axioms gamma_two

end YMYMG.GeneratedAudit
