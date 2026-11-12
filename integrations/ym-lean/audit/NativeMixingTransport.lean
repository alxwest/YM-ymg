import MixingRateTransport
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! The transformed mixing acts on the actual recursive native insertions.
This proves covariance of the differential-plus-mixing part. Transport of
the quantum-exact primitive is a separate obligation. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.MixingTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre
open YMYMG.DictionaryRenormalization YMYMG.CouplingTaylor
open YMYMG.LegendreTransport YMYMG.ScaleTransport
variable {G : CompactSimpleGaugeGroup}
variable {B : InvariantForm G} {e : ColorFrame B}
  {lift : QuantumObservableLift G} {anomaly : ℝ → LocalAnomalyCoefficients G}
  {Q : QuantumWardLimit G} {L : ℝ → InsertedFlowFamily G} {W : WardContinuumData G}

theorem finiteInsertion_add (h : lift.Compatible e anomaly Q)
    (g : ℝ) (p t : InvariantInsertionLabel G) (x : Spacetime) :
    lift.finiteInsertion (L g) g (p+t) x =
      lift.finiteInsertion (L g) g p x + lift.finiteInsertion (L g) g t x := by
  funext loop IR UV legs q
  simp only [QuantumObservableLift.finiteInsertion, ← insertionFunctional_apply,
    h.linear_add, map_add, Finset.sum_add_distrib, Pi.add_apply]

theorem finiteInsertion_smul (h : lift.Compatible e anomaly Q)
    (g c : ℝ) (p : InvariantInsertionLabel G) (x : Spacetime) :
    lift.finiteInsertion (L g) g (c • p) x = (c : ℂ) • lift.finiteInsertion (L g) g p x := by
  funext loop IR UV legs q
  simp only [QuantumObservableLift.finiteInsertion, ← insertionFunctional_apply,
    h.linear_smul, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem insertion_coupling_smooth (hl : lift.LimitCompatible L W)
    (p : InvariantInsertionLabel G) (x : Spacetime) (s : CutoffScales)
    (loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    ContDiff ℝ ∞ (fun g => lift.finiteInsertion (L g) g p x loop s.infrared s.ultraviolet legs q) := by
  simpa only [Function.comp_def] using!
    (hl.coupling_momentum_smooth p x loop s.infrared s.ultraviolet
      s.infrared_pos s.ordered legs).comp (contDiff_id.prodMk contDiff_const)

theorem insertion_flowJet_add (h : lift.Compatible e anomaly Q)
    (hl : lift.LimitCompatible L W) (p t : InvariantInsertionLabel G)
    (x : Spacetime) (s : CutoffScales) :
    flowJet (fun g => lift.finiteInsertion (L g) g (p+t) x) s =
      flowJet (fun g => lift.finiteInsertion (L g) g p x) s +
      flowJet (fun g => lift.finiteInsertion (L g) g t x) s := by
  funext r l legs q
  change jet r (fun g => lift.finiteInsertion (L g) g (p+t) x l s.infrared s.ultraviolet legs q) =
    jet r (fun g => lift.finiteInsertion (L g) g p x l s.infrared s.ultraviolet legs q) +
    jet r (fun g => lift.finiteInsertion (L g) g t x l s.infrared s.ultraviolet legs q)
  simp only [finiteInsertion_add h, Pi.add_apply]
  exact jet_add r _ _ (insertion_coupling_smooth hl p x s l legs q)
    (insertion_coupling_smooth hl t x s l legs q)

theorem insertion_flowJet_smul (h : lift.Compatible e anomaly Q)
    (c : ℝ) (p : InvariantInsertionLabel G) (x : Spacetime) (s : CutoffScales) :
    flowJet (fun g => lift.finiteInsertion (L g) g (c • p) x) s =
      (c : ℂ) • flowJet (fun g => lift.finiteInsertion (L g) g p x) s := by
  funext r l legs q
  change jet r (fun g => lift.finiteInsertion (L g) g (c • p) x l s.infrared s.ultraviolet legs q) =
    (c : ℂ)*jet r (fun g => lift.finiteInsertion (L g) g p x l s.infrared s.ultraviolet legs q)
  simp only [finiteInsertion_smul h, Pi.smul_apply, smul_eq_mul]
  exact jet_const_mul r (c : ℂ) _

def liftedLinear (A : ScaleCouplingFamily G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (lift : ℝ → QuantumObservableLift G) (mu : ℝ)
    {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G} {W : WardContinuumData G}
    (h : (lift mu).Compatible e anomaly Q) (hl : (lift mu).LimitCompatible (L mu) W)
    (s : CutoffScales) (x : Spacetime) : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G where
  toFun p := liftedGamma A L lift mu s p x
  map_add' p t := by
    simp only [liftedGamma, directionalGamma, insertion_flowJet_add h hl, insertion_add]
  map_smul' c p := by
    simp only [liftedGamma, directionalGamma, insertion_flowJet_smul h, insertion_smul,
      RingHom.id_apply]
    rfl

variable {S : FixedFlowSystem e}

def familyLiftedLinear (family : LocalWardFlowFamily S) (mu : ℝ) (hmu : 0 < mu)
    (s : CutoffScales) (x : Spacetime) : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G :=
  liftedLinear S.background S.insertions
    (positiveScaleExtension S.referenceScale family.lift) mu
    (by simpa only [positiveScaleExtension, dif_pos hmu] using!
      (family.full_ward ⟨mu,hmu⟩).same_dictionary)
    (by simpa only [positiveScaleExtension, dif_pos hmu] using!
      (family.full_ward ⟨mu,hmu⟩).same_dictionary_limit) s x

theorem family_dictionaryChange (family : LocalWardFlowFamily S) (D : Direction G)
    (a : RenormalizationScale → ℝ) (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (x : Spacetime) :
    familyLiftedLinear (changeFamily family D a) mu hmu s x =
      dictionaryChange (familyLiftedLinear family mu hmu s x) D
        (positiveScaleExtension S.referenceScale a mu) := by
  apply LinearMap.ext
  intro p
  rw [dictionaryChange_apply]
  exact family_liftedGamma_change family D a mu hmu s p x

theorem real_weight_deriv (a : ℝ → ℝ) (w mu : ℝ) (ha : DifferentiableAt ℝ a mu) :
    deriv (fun nu => ((a nu*w : ℝ) : ℂ)) mu = ((deriv a mu*w : ℝ) : ℂ) :=
  ((ha.hasDerivAt.mul_const w).ofReal_comp).deriv

theorem family_mixing_change (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G) (hq : D.weight D.lower = 0)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0))
    (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime) :
    let ae := positiveScaleExtension S.referenceScale a
    let J := familyLiftedLinear family mu hmu s x
    mixingAction (changeMixing N.mixing D hq N.beta ae ha) mu
      (fun label => liftedGamma S.background S.insertions
        (positiveScaleExtension S.referenceScale (changeFamily family D a).lift) mu s label x) p =
      mixingAction N.mixing mu J p +
      (ae mu*D.weight p : ℝ) • amplitudeDelay (mixingAction N.mixing mu J D.lower) -
      (mu*deriv ae mu*D.weight p : ℝ) • amplitudeDelay (J D.lower) -
      (2*ae mu*D.weight p : ℝ) • scalarAction N.beta (firstDelay (J D.lower)) := by
  dsimp only
  change mixingAction _ mu (familyLiftedLinear (changeFamily family D a) mu hmu s x) p = _
  rw [family_dictionaryChange]
  exact changeMixing_action_expanded N.mixing D hq N.beta _ ha mu _ p

/-- The actual differential-plus-mixing part is covariant. All extra
derivative terms cancel before any limit is taken, for 0 < mu < UV. -/
theorem family_differential_mixing_change (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G) (hq : D.weight D.lower = 0)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0))
    (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (hs : mu < s.ultraviolet)
    (p : InvariantInsertionLabel G) (x : Spacetime) :
    let ae := positiveScaleExtension S.referenceScale a
    let J := fun nu label => liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale family.lift) nu s label x
    let J' := fun nu label => liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale (changeFamily family D a).lift) nu s label x
    differentialPart N.beta N.fields (fun nu => J' nu p) mu +
      mixingAction (changeMixing N.mixing D hq N.beta ae ha) mu (J' mu) p =
      (differentialPart N.beta N.fields (fun nu => J nu p) mu + mixingAction N.mixing mu (J mu) p) +
      (ae mu*D.weight p : ℝ) • amplitudeDelay
        (differentialPart N.beta N.fields (fun nu => J nu D.lower) mu +
          mixingAction N.mixing mu (J mu) D.lower) := by
  dsimp only
  rw [family_differential_change family N D a ha mu hmu s hs p x,
    family_mixing_change family N D hq a ha mu hmu s p x]
  have hd : DifferentiableAt ℝ (positiveScaleExtension S.referenceScale a) mu :=
    (ha.contDiffAt (Ioi_mem_nhds hmu)).differentiableAt (by simp)
  rw [real_weight_deriv _ _ _ hd, amplitudeDelay_add]
  funext r l legs q
  simp only [familyLiftedLinear, liftedLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

#print axioms finiteInsertion_add
#print axioms finiteInsertion_smul
#print axioms insertion_coupling_smooth
#print axioms insertion_flowJet_add
#print axioms insertion_flowJet_smul
#print axioms liftedLinear
#print axioms familyLiftedLinear
#print axioms family_dictionaryChange
#print axioms real_weight_deriv
#print axioms family_mixing_change
#print axioms family_differential_mixing_change
end YMYMG.MixingTransport
