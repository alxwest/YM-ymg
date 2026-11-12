import IncomingRecoveryLinear

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! A common output enumeration is chosen only to combine recovery
witnesses. No independence or injectivity of quantum fields is assumed. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.IncomingRecovery
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.IncomingExpansion YMYMG.OutputRecoveryCoherent

variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
    {L : ℝ → InsertedFlowFamily G} {transport : SameTheoryWardTransportData e L}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}

theorem lifted_enumeration (basis : OPE.FilteredBasis G) (cutoff : ℕ) {n : ℕ}
    (index : Fin n → basis.Index) (hinj : Function.Injective index)
    (hactive : Finset.univ.image index = basis.active cutoff)
    (c : ℕ → ℕ → basis.Index → ℂ) (r l : ℕ) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs) :
    liftedOutputDistribution lift W (fun i => basis.label (index i))
      (fun r l i => c r l (index i)) r l legs test =
      ∑ i ∈ basis.active cutoff, convolve (fun r l => c r l i)
        (fun r l => lift.physicalInsertion W (basis.label i) r l legs test) r l := by
  rw [← hactive, Finset.sum_image (fun _ _ _ _ h => hinj h)]
  simp only [liftedOutputDistribution, convolve, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]

theorem recovery_enumeration (basis : OPE.FilteredBasis G) (cutoff : ℕ) {n m : ℕ}
    (index : Fin n → basis.Index) (next : Fin m → basis.Index)
    (hi : Function.Injective index) (hn : Function.Injective next)
    (hindex : Finset.univ.image index = basis.active cutoff)
    (hnext : Finset.univ.image next = basis.active cutoff)
    (v : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ)
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff
      (fun i => basis.label (index i)) v (fun r l i => c r l (index i))) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff
      (fun i => basis.label (next i)) v (fun r l i => c r l (next i)) := by
  obtain ⟨hc, hl, hw, ha, hf, hnil, hs, hd, hg, p, hp, he⟩ := h
  have hfind (i : Fin m) : ∃ j : Fin n, index j = next i := by
    have hm : next i ∈ basis.active cutoff := hnext ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [← hindex] at hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact ⟨j, hj⟩
  refine ⟨hc, hl, hw, ha, hf, hnil, hs, ?_, ?_, p, hp, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hfind i
    simpa only [hj] using hd j
  · intro r l i hrl
    obtain ⟨j, hj⟩ := hfind i
    simpa only [hj] using hg r l j hrl
  · intro r l legs test hcompact hnonex
    have ht := he r l legs test hcompact hnonex
    rw [lifted_enumeration basis cutoff index hi hindex c] at ht
    rw [lifted_enumeration basis cutoff next hn hnext c]
    exact ht

theorem coherent_add (basis : OPE.FilteredBasis G)
    {v w : BigradedMonomialVector G} {c d : ℕ → ℕ → basis.Index → ℂ}
    (h : CoherentRecovery basis e L transport lift W Q v c)
    (k : CoherentRecovery basis e L transport lift W Q w d) :
    CoherentRecovery basis e L transport lift W Q (v+w) (c+d) := by
  intro cutoff
  obtain ⟨n, index, hi, hs, hv⟩ := h cutoff
  obtain ⟨m, other, ho, ht, hw⟩ := k cutoff
  have hw' := recovery_enumeration basis cutoff other index ho hi ht hs w d hw
  exact ⟨n, index, hi, hs, recovery_add hv hw'⟩

theorem coherent_smul (basis : OPE.FilteredBasis G)
    {v : BigradedMonomialVector G} {c : ℕ → ℕ → basis.Index → ℂ}
    (h : CoherentRecovery basis e L transport lift W Q v c) (a : ℂ) :
    CoherentRecovery basis e L transport lift W Q (a • v) (a • c) := by
  intro cutoff
  obtain ⟨n, index, hi, hs, hv⟩ := h cutoff
  exact ⟨n, index, hi, hs, recovery_smul hv a⟩

theorem coherent_delay (basis : OPE.FilteredBasis G)
    {v : BigradedMonomialVector G} {c : ℕ → ℕ → basis.Index → ℂ}
    (h : CoherentRecovery basis e L transport lift W Q v c) :
    CoherentRecovery basis e L transport lift W Q (delay v) (delay c) := by
  intro cutoff
  obtain ⟨n, index, hi, hs, hv⟩ := h cutoff
  refine ⟨n, index, hi, hs, ?_⟩
  have hc : (fun r l i => delay c r l (index i)) = delay (fun r l i => c r l (index i)) := by
    funext r l i
    obtain r | r | r := r <;> cases l <;> rfl
  rw [hc]
  exact recovery_delay hv

/-- All orders and all cutoffs share the expanded coefficient table.
Each native exact primitive is expanded by the same finite operation. -/
theorem expand_recovery {I : Type*} (basis : OPE.FilteredBasis G)
    (weight : I → ℂ) (lower : I) (n : ℕ)
    (raw : (Fin n → I) → BigradedMonomialVector G)
    (c : (Fin n → I) → ℕ → ℕ → basis.Index → ℂ)
    (h : ∀ xs, CoherentRecovery basis e L transport lift W Q (raw xs) (c xs))
    (labels : Fin n → I) :
    CoherentRecovery basis e L transport lift W Q
      (expandInputs jetDelay weight lower n raw labels)
      (expandInputs jetDelay weight lower n c labels) := by
  induction n with
  | zero => exact h labels
  | succ n ih =>
    apply coherent_add basis
    · exact ih _ _ (fun xs => h (Fin.cons (labels 0) xs)) _
    · apply coherent_smul basis
      apply coherent_delay basis
      exact ih _ _ (fun xs => h (Fin.cons lower xs)) _

#print axioms lifted_enumeration
#print axioms recovery_enumeration
#print axioms coherent_add
#print axioms coherent_smul
#print axioms coherent_delay
#print axioms expand_recovery
end YMYMG.IncomingRecovery
