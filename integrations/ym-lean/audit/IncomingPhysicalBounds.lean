import GeneratedIncomingRaw

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Incoming locality, graph order and collision bounds. A replacement
is used only when its actual weight is nonzero. -/
noncomputable section
open Filter
namespace YMYMG.IncomingPhysicalBounds
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.IncomingExpansion YMYMG.GeneratedIncomingRaw
open YMYMG.GeneratedOutputTransport

theorem expand_restrict {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (P : E → Prop)
    (hadd : ∀ x y, P x → P y → P (x+y))
    (hsmul : ∀ (a : ℂ) x, P x → P (a • x)) (hshift : ∀ x, P x → P (s x))
    (n : ℕ) (admissible : Fin n → I → Prop)
    (F : (Fin n → I) → E) (hF : ∀ xs, (∀ i, admissible i (xs i)) → P (F xs))
    (labels : Fin n → I) (hlabels : ∀ i, admissible i (labels i))
    (hlower : ∀ i, w (labels i) ≠ 0 → admissible i lower) :
    P (expandInputs s w lower n F labels) := by
  induction n with
  | zero => exact hF labels hlabels
  | succ n ih =>
    have hp : P (expandInputs s w lower n (fun xs => F (Fin.cons (labels 0) xs))
        (Fin.tail labels)) := by
      apply ih (fun i => admissible i.succ) _ _ _
        (fun i => hlabels i.succ) (fun i => hlower i.succ)
      intro xs hx
      apply hF
      intro i
      exact Fin.cases (hlabels 0) (fun j => hx j) i
    by_cases hw : w (labels 0) = 0
    · simpa only [expandInputs, hw, zero_smul, add_zero] using hp
    · apply hadd _ _ hp
      apply hsmul
      apply hshift
      apply ih (fun i => admissible i.succ) _ _ _
        (fun i => hlabels i.succ) (fun i => hlower i.succ)
      intro xs hx
      apply hF
      intro i
      exact Fin.cases (hlower 0 hw) (fun j => hx j) i

theorem expand_graph {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (w : I → ℂ) (lower : I) (n : ℕ) (F : (Fin n → I) → ℕ → ℕ → E)
    (hF : ∀ xs r l, r < 2*l → F xs r l = 0) (labels : Fin n → I)
    (r l : ℕ) (hrl : r < 2*l) : expandInputs jetDelay w lower n F labels r l = 0 := by
  apply expand_transfer jetDelay w lower
    (fun J : ℕ → ℕ → E => ∀ r l, r < 2*l → J r l = 0)
    (fun _ _ hU hV r l hrl => by simp only [Pi.add_apply, hU r l hrl, hV r l hrl, add_zero])
    (fun a _ hU r l hrl => by simp only [Pi.smul_apply, hU r l hrl, smul_zero])
    (fun J hJ r l hrl => ?_) n F hF labels r l hrl
  obtain r | r | r := r <;> cases l
  all_goals first | rfl | exact hJ _ _ (by omega)

theorem scaling_zero {n : ℕ} (input : Fin (n+1) → ℕ) (output : ℕ) :
    OPE.PartialScalingBounds (0 : OPE.MultiDistribution n) input output := by
  intro S f hf δ hδ
  simpa only [LinearMap.zero_apply, mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))

theorem scaling_add {n : ℕ} (U V : OPE.MultiDistribution n)
    (input : Fin (n+1) → ℕ) (output : ℕ)
    (hU : OPE.PartialScalingBounds U input output)
    (hV : OPE.PartialScalingBounds V input output) :
    OPE.PartialScalingBounds (U+V) input output := by
  simpa only [neg_smul, one_smul, sub_neg_eq_add] using
    scaling_sub_smul U V (-1) input output hU hV

theorem scaling_smul {n : ℕ} (a : ℂ) (U : OPE.MultiDistribution n)
    (input : Fin (n+1) → ℕ) (output : ℕ)
    (hU : OPE.PartialScalingBounds U input output) :
    OPE.PartialScalingBounds (a • U) input output := by
  simpa only [neg_smul, zero_sub, neg_neg] using
    scaling_sub_smul 0 U (-a) input output (scaling_zero input output) hU

variable {G : CompactSimpleGaugeGroup} {basis : OPE.FilteredBasis G}

theorem clusterInputDegrees_tuple {n : ℕ} (xs : Fin (n+1) → basis.Index) :
    clusterInputDegrees (fun i => xs i.castSucc) (xs (Fin.last n)) =
      fun i => OPE.dimension (basis.label (xs i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [clusterInputDegrees]
  · simp [clusterInputDegrees, j.is_lt]

def incomingPhysical (E : GeneratedEuclideanData basis) (w : basis.Index → ℂ)
    (lower : basis.Index) (r l n : ℕ) (inputs : Fin n → basis.Index)
    (last output : basis.Index) : OPE.MultiDistribution n :=
  expandInputs jetDelay w lower (n+1)
    (fun xs r l => E.physical r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output)
    (Fin.lastCases last inputs) r l

theorem incomingPhysical_apply (E : GeneratedEuclideanData basis) (w : basis.Index → ℂ)
    (lower : basis.Index) (r l n : ℕ) (inputs : Fin n → basis.Index)
    (last output : basis.Index) (f : OPE.RelativeTest n) :
    incomingPhysical E w lower r l n inputs last output f =
      expandInputs jetDelay w lower (n+1)
        (fun xs r l => E.physical r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output f)
        (Fin.lastCases last inputs) r l :=
  expand_distribution_apply w lower (n+1) _ _ r l f

theorem incomingPhysical_scaling (E : GeneratedEuclideanData basis)
    (h : ∀ r l n inputs last output, OPE.PartialScalingBounds (E.physical r l n inputs last output)
      (clusterInputDegrees inputs last) (OPE.dimension (basis.label output)))
    (w : basis.Index → ℂ) (lower : basis.Index)
    (hw : ∀ p, w p ≠ 0 → OPE.dimension (basis.label lower) = OPE.dimension (basis.label p))
    (r l n : ℕ) (inputs : Fin n → basis.Index) (last output : basis.Index) :
    OPE.PartialScalingBounds (incomingPhysical E w lower r l n inputs last output)
      (clusterInputDegrees inputs last) (OPE.dimension (basis.label output)) := by
  let labels : Fin (n+1) → basis.Index := Fin.lastCases last inputs
  let degrees := clusterInputDegrees inputs last
  let out := OPE.dimension (basis.label output)
  have hdegrees : degrees = fun i => OPE.dimension (basis.label (labels i)) := by
    simpa only [labels, degrees, Fin.lastCases_castSucc, Fin.lastCases_last] using
      clusterInputDegrees_tuple labels
  have hshift (J : ℕ → ℕ → OPE.MultiDistribution n)
      (hJ : ∀ r l, OPE.PartialScalingBounds (J r l) degrees out) :
      ∀ r l, OPE.PartialScalingBounds (jetDelay J r l) degrees out := by
    intro r l
    obtain r | r | r := r <;> cases l
    all_goals first | exact scaling_zero degrees out | exact hJ _ _
  have hF (xs : Fin (n+1) → basis.Index)
      (hx : ∀ i, OPE.dimension (basis.label (xs i)) = OPE.dimension (basis.label (labels i))) :
      ∀ r l, OPE.PartialScalingBounds
        (E.physical r l n (fun i => xs i.castSucc) (xs (Fin.last n)) output) degrees out := by
    intro r l
    have hd : clusterInputDegrees (fun i => xs i.castSucc) (xs (Fin.last n)) = degrees := by
      rw [clusterInputDegrees_tuple, hdegrees]
      funext i
      exact hx i
    rw [← hd]
    exact h r l n _ _ output
  exact expand_restrict jetDelay w lower
    (fun J : ℕ → ℕ → OPE.MultiDistribution n => ∀ r l, OPE.PartialScalingBounds (J r l) degrees out)
    (fun _ _ hU hV r l => scaling_add _ _ degrees out (hU r l) (hV r l))
    (fun a _ hU r l => scaling_smul a _ degrees out (hU r l))
    hshift (n+1)
    (fun i p => OPE.dimension (basis.label p) = OPE.dimension (basis.label (labels i)))
    _ hF labels (fun _ => rfl) (fun i => hw (labels i)) r l

#print axioms expand_restrict
#print axioms expand_graph
#print axioms scaling_zero
#print axioms scaling_add
#print axioms scaling_smul
#print axioms clusterInputDegrees_tuple
#print axioms incomingPhysical_apply
#print axioms incomingPhysical_scaling
end YMYMG.IncomingPhysicalBounds
