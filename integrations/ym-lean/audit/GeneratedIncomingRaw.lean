import IncomingNativeLimits
import GeneratedOutputTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! One distribution-valued raw table fixed by the changed native extractor.
This transports the raw side from existing compatible data; it does not
choose physical output coefficients or assert full compatibility. -/
noncomputable section
open MeasureTheory Filter
namespace YMYMG.GeneratedIncomingRaw
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization YMYMG.IncomingExpansion
open YMYMG.GeneratedOutputTransport

def evaluateJets {n : ℕ} (f : OPE.RelativeTest n) :
    (ℕ → ℕ → OPE.MultiDistribution n) →ₗ[ℂ] (ℕ → ℕ → ℂ) where
  toFun F r l := F r l f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluateJets_delay {n : ℕ} (f : OPE.RelativeTest n)
    (F : ℕ → ℕ → OPE.MultiDistribution n) :
    evaluateJets f (jetDelay F) = jetDelay (evaluateJets f F) := by
  funext r l
  exact map_delay (fun T : OPE.MultiDistribution n => T f) (by simp) F r l

theorem expand_distribution_apply {I : Type*} {n : ℕ}
    (w : I → ℂ) (lower : I) (count : ℕ)
    (F : (Fin count → I) → ℕ → ℕ → OPE.MultiDistribution n)
    (labels : Fin count → I) (order loop : ℕ) (f : OPE.RelativeTest n) :
    expandInputs jetDelay w lower count F labels order loop f =
      expandInputs jetDelay w lower count (fun xs r l => F xs r l f) labels order loop := by
  have h := expand_natural jetDelay jetDelay (evaluateJets f) (evaluateJets_delay f)
    w lower count F labels
  exact congrFun (congrFun h order) loop

theorem local_zero (n : ℕ) : OPE.IsLocalMultiDistribution (0 : OPE.MultiDistribution n) := by
  intro K hK
  exact ⟨0, 0, le_rfl, by intro f hf; simp⟩

theorem local_add {n : ℕ} (U V : OPE.MultiDistribution n)
    (hU : OPE.IsLocalMultiDistribution U) (hV : OPE.IsLocalMultiDistribution V) :
    OPE.IsLocalMultiDistribution (U+V) := by
  simpa only [neg_smul, one_smul, sub_neg_eq_add] using local_sub_smul U V (-1) hU hV

theorem local_smul {n : ℕ} (a : ℂ) (U : OPE.MultiDistribution n)
    (hU : OPE.IsLocalMultiDistribution U) : OPE.IsLocalMultiDistribution (a • U) := by
  simpa only [neg_smul, zero_sub, neg_neg] using local_sub_smul 0 U (-a) (local_zero n) hU

theorem expand_local {I : Type*} {n : ℕ} (w : I → ℂ) (lower : I) (count : ℕ)
    (F : (Fin count → I) → ℕ → ℕ → OPE.MultiDistribution n)
    (hF : ∀ xs r l, OPE.IsLocalMultiDistribution (F xs r l))
    (labels : Fin count → I) (order loop : ℕ) :
    OPE.IsLocalMultiDistribution (expandInputs jetDelay w lower count F labels order loop) := by
  apply expand_transfer jetDelay w lower
    (fun J : ℕ → ℕ → OPE.MultiDistribution n => ∀ r l, OPE.IsLocalMultiDistribution (J r l))
    (fun _ _ hU hV r l => local_add _ _ (hU r l) (hV r l))
    (fun a _ hU r l => local_smul a _ (hU r l))
    (fun J hJ r l => ?_) count F hF labels order loop
  obtain r | r | r := r <;> cases l
  all_goals first | exact local_zero n | exact hJ _ _

variable {G : CompactSimpleGaugeGroup} {basis : OPE.FilteredBasis G}

def incomingRaw (E : GeneratedEuclideanData basis) (w : basis.Index → ℂ)
    (lower : basis.Index) (order loop n : ℕ) (inputs : Fin n → basis.Index)
    (last : basis.Index) (output : LocalMonomial G) : OPE.MultiDistribution n :=
  expandInputs jetDelay w lower (n+1)
    (fun xs r l => E.raw r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output)
    (Fin.lastCases last inputs) order loop

theorem incomingRaw_apply (E : GeneratedEuclideanData basis) (w : basis.Index → ℂ)
    (lower : basis.Index) (order loop n : ℕ) (inputs : Fin n → basis.Index)
    (last : basis.Index) (output : LocalMonomial G) (f : OPE.RelativeTest n) :
    incomingRaw E w lower order loop n inputs last output f =
      expandInputs jetDelay w lower (n+1)
        (fun xs r l => E.raw r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output f)
        (Fin.lastCases last inputs) order loop :=
  expand_distribution_apply w lower (n+1) _ _ order loop f

theorem incomingRaw_local (E : GeneratedEuclideanData basis)
    (h : ∀ r l n inputs last output, OPE.IsLocalMultiDistribution (E.raw r l n inputs last output))
    (w : basis.Index → ℂ) (lower : basis.Index) (order loop n : ℕ)
    (inputs : Fin n → basis.Index) (last : basis.Index) (output : LocalMonomial G) :
    OPE.IsLocalMultiDistribution (incomingRaw E w lower order loop n inputs last output) :=
  expand_local w lower (n+1) _
    (fun xs r l => h r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output) _ order loop

variable {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}
    {transport : SameTheoryWardTransportData e (S.insertions S.referenceScale.val)}

/-- This is the literal native raw_limit condition for the new table and
changed lift, at every order, loop, arity, input, monomial output and allowed test. -/
theorem incomingRaw_limit (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (D : Direction G)
    (lower : basis.Index) (hlower : basis.label lower = D.lower) (a : ℝ)
    (order loop n : ℕ) (inputs : Fin n → basis.Index) (last : basis.Index)
    (output : LocalMonomial G) (f : OPE.RelativeTest n) (hf : OPE.MultiOffDiagonal f) :
    Tendsto (fun UV => ∫ r, S.liftedCouplingCoefficient (change lift D a)
      (fun i => basis.label (inputs i)) (basis.label last) output loop order UV r * f r)
      atTop (nhds (incomingRaw E (fun p => ((a * D.weight (basis.label p) : ℝ) : ℂ))
        lower order loop n inputs last output f)) := by
  rw [incomingRaw_apply]
  simpa only [tupleJet, Fin.lastCases_castSucc, Fin.lastCases_last] using!
    tupleJet_limit_change S lift h.regularity D basis.label lower hlower a output f hf
      (fun xs r l => E.raw r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output f)
      (fun xs r l => h.raw_limit r l n _ _ output f hf)
      (Fin.lastCases last inputs) order loop

#print axioms evaluateJets
#print axioms evaluateJets_delay
#print axioms expand_distribution_apply
#print axioms local_zero
#print axioms local_add
#print axioms local_smul
#print axioms expand_local
#print axioms incomingRaw_apply
#print axioms incomingRaw_local
#print axioms incomingRaw_limit
end YMYMG.GeneratedIncomingRaw
