import OutputCoefficientShear
import DictionaryInsertionTransport
import YangMills.QuantumOutputRecovery

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Transport the actual native output recovery relation at a fixed cutoff.
The raw vector and its exact primitive are retained. This does not prove
that the cutoff-dependent corrected coefficients form one global family. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.OutputRecovery
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization

variable {G : CompactSimpleGaugeGroup} {n : ℕ} {B : InvariantForm G}
  {e : ColorFrame B} {anomaly : ℝ → LocalAnomalyCoefficients G}
  {lift : QuantumObservableLift G} {Q : QuantumWardLimit G}

theorem liftedOutput_value (W : WardContinuumData G)
    (labels : Fin n → InvariantInsertionLabel G) (c : ℕ → ℕ → Fin n → ℂ)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    liftedOutputDistribution lift W labels c order loop legs test =
      assemble c (fun i r l => lift.physicalInsertion W (labels i) r l legs test)
        order loop := by
  simp only [liftedOutputDistribution, assemble, convolve,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The finite inverse coefficient correction cancels the changed dictionary
on the literal native physical output distribution, on every test. -/
theorem liftedOutput_corrected (h : lift.Compatible e anomaly Q)
    (D : Direction G) (hq : D.weight D.lower = 0) (a : ℝ)
    (W : WardContinuumData G) (labels : Fin n → InvariantInsertionLabel G)
    (k : Fin n) (hk : labels k = D.lower) (c : ℕ → ℕ → Fin n → ℂ)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    liftedOutputDistribution (change lift D a) W labels
      (corrected (fun i => D.weight (labels i)) k a c) order loop legs test =
        liftedOutputDistribution lift W labels c order loop legs test := by
  simp only [liftedOutput_value, physicalInsertion_change h D a]
  simpa only [assemble, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hk, Complex.ofReal_mul] using!
      assemble_cancel (fun i => D.weight (labels i)) k a c
        (fun i r l => lift.physicalInsertion W (labels i) r l legs test)
        (by rw [hk]; exact hq) order loop

/-- All fields of the fixed-cutoff native recovery relation are preserved.
This is conditional on an original recovery and an active lower label. -/
theorem recovery_corrected {L : ℝ → InsertedFlowFamily G}
    {transport : SameTheoryWardTransportData e L} {W : WardContinuumData G}
    (D : Direction G) (hq : D.weight D.lower = 0) (a : ℝ) (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G) (k : Fin n) (hk : labels k = D.lower)
    (raw : BigradedMonomialVector G) (c : ℕ → ℕ → Fin n → ℂ)
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw c) :
    QuantumPhysicalOutputRecovery e L transport (change lift D a) W Q cutoff labels raw
      (corrected (fun i => D.weight (labels i)) k a c) := by
  obtain ⟨hcomp, hlimit, hward, haction, hfiltered, hnil, hsmooth, hlabels, hgraph,
    primitive, hsupport, heq⟩ := h
  refine ⟨compatible hcomp D a, limitCompatible hcomp hlimit D a,
    hward, haction, hfiltered, hnil, hsmooth, hlabels,
    corrected_graph_order _ k a c hgraph, primitive, hsupport, ?_⟩
  intro order loop legs test hcompact hnonex
  rw [liftedOutput_corrected hcomp D hq a W labels k hk]
  exact heq order loop legs test hcompact hnonex

/-- If the correction vanishes on all active labels, coefficients need no
change. This includes cutoffs below the lower label's engineering degree. -/
theorem recovery_fixed {L : ℝ → InsertedFlowFamily G}
    {transport : SameTheoryWardTransportData e L} {W : WardContinuumData G}
    (D : Direction G) (a : ℝ) (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G)
    (hw : ∀ i, D.weight (labels i) = 0)
    (raw : BigradedMonomialVector G) (c : ℕ → ℕ → Fin n → ℂ)
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw c) :
    QuantumPhysicalOutputRecovery e L transport (change lift D a) W Q cutoff labels raw c := by
  obtain ⟨hcomp, hlimit, hward, haction, hfiltered, hnil, hsmooth, hlabels, hgraph,
    primitive, hsupport, heq⟩ := h
  refine ⟨compatible hcomp D a, limitCompatible hcomp hlimit D a,
    hward, haction, hfiltered, hnil, hsmooth, hlabels,
    hgraph, primitive, hsupport, ?_⟩
  intro order loop legs test hcompact hnonex
  have he : liftedOutputDistribution (change lift D a) W labels c order loop legs test =
      liftedOutputDistribution lift W labels c order loop legs test := by
    simp only [liftedOutput_value, assemble, physicalInsertion_change hcomp D a,
      hw, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
  rw [he]
  exact heq order loop legs test hcompact hnonex

theorem inactive_weights (D : Direction G) (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G)
    (hlabels : ∀ i, intrinsicEngineeringDimension (labels i) < cutoff)
    (hlower : cutoff ≤ intrinsicEngineeringDimension D.lower) :
    ∀ i, D.weight (labels i) = 0 := by
  intro i
  by_contra hw
  have hf := D.filtered (labels i) hw
  have hi := hlabels i
  omega

/-- Existence of an outgoing recovery is equivalent at a fixed cutoff,
provided the lower label is active or the correction is zero on the sector.
The witnesses may depend on the cutoff; this is not global coherence. -/
theorem recovery_exists_iff {L : ℝ → InsertedFlowFamily G}
    {transport : SameTheoryWardTransportData e L} {W : WardContinuumData G}
    (D : Direction G) (hq : D.weight D.lower = 0) (a : ℝ) (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G)
    (hactive : (∃ k, labels k = D.lower) ∨ (∀ i, D.weight (labels i) = 0))
    (raw : BigradedMonomialVector G) :
    (∃ c, QuantumPhysicalOutputRecovery e L transport (change lift D a) W Q
      cutoff labels raw c) ↔
    (∃ c, QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw c) := by
  have forward (original : QuantumObservableLift G) (b : ℝ)
      (h : ∃ c, QuantumPhysicalOutputRecovery e L transport original W Q
        cutoff labels raw c) :
      ∃ c, QuantumPhysicalOutputRecovery e L transport (change original D b) W Q
        cutoff labels raw c := by
    obtain ⟨c, hc⟩ := h
    rcases hactive with ⟨k, hk⟩ | hw
    · exact ⟨_, recovery_corrected D hq b cutoff labels k hk raw c hc⟩
    · exact ⟨c, recovery_fixed D b cutoff labels hw raw c hc⟩
  constructor
  · intro h
    simpa only [change_inverse D a hq] using forward (change lift D a) (-a) h
  · exact forward lift a

def monomialAnnulus (G : CompactSimpleGaugeGroup) (small large : ℕ) :
    Finset (LocalMonomial G) := by
  classical
  exact monomialsBelow G large \ monomialsBelow G small

/-- The raw cutoff is the literal monomial projection. Enlarging it adds
an annulus of raw monomials, not a projection defined by the quantum lift. -/
theorem raw_cutoff_difference (W : WardContinuumData G) (raw : BigradedMonomialVector G)
    (small large : ℕ) (h : small ≤ large) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    rawOutputDistribution W large raw order loop legs test -
        rawOutputDistribution W small raw order loop legs test =
      ∑ m ∈ monomialAnnulus G small large,
        ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
          raw a.val b.val m * W.physical .single (order-a.val) (loop-b.val)
            (fun _ : Fin 1 => m) legs test := by
  classical
  have hsub : monomialsBelow G small ⊆ monomialsBelow G large := by
    intro m hm
    obtain ⟨ha, hd⟩ := (mem_monomialsBelow_iff small m).mp hm
    exact (mem_monomialsBelow_iff large m).mpr ⟨ha, lt_of_lt_of_le hd h⟩
  simp only [rawOutputDistribution, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simpa only [monomialAnnulus] using! (eq_sub_of_add_eq
    (Finset.sum_sdiff (f := fun m : LocalMonomial G =>
      ∑ a : Fin (order + 1), ∑ b : Fin (loop + 1),
        raw a.val b.val m * W.physical .single (order-a.val) (loop-b.val)
          (fun _ : Fin 1 => m) legs test) hsub)).symm

/-- Any two actual recovery witnesses must satisfy this cutoff comparison.
The two generated-Q remainders remain explicit; neither is declared zero. -/
theorem recovery_cutoff_difference {nsmall nlarge : ℕ}
    {L : ℝ → InsertedFlowFamily G} {transport : SameTheoryWardTransportData e L}
    {W : WardContinuumData G} (small large : ℕ)
    (smallLabels : Fin nsmall → InvariantInsertionLabel G)
    (largeLabels : Fin nlarge → InvariantInsertionLabel G)
    (raw : BigradedMonomialVector G)
    (csmall : ℕ → ℕ → Fin nsmall → ℂ) (clarge : ℕ → ℕ → Fin nlarge → ℂ)
    (hsmall : QuantumPhysicalOutputRecovery e L transport lift W Q small
      smallLabels raw csmall)
    (hlarge : QuantumPhysicalOutputRecovery e L transport lift W Q large
      largeLabels raw clarge) :
    ∃ psmall plarge : BigradedMonomialVector G,
      (∀ order loop m, psmall order loop m ≠ 0 → m ∈ outputPrimitiveMonomials G small) ∧
      (∀ order loop m, plarge order loop m ≠ 0 → m ∈ outputPrimitiveMonomials G large) ∧
      ∀ order loop legs (test : JointMomentumTest 1 legs),
        HasCompactSupport test → NonexceptionalSupport .single test →
        rawOutputDistribution W large raw order loop legs test -
          rawOutputDistribution W small raw order loop legs test =
        (liftedOutputDistribution lift W largeLabels clarge order loop legs test -
          liftedOutputDistribution lift W smallLabels csmall order loop legs test) +
        (rawOutputDistribution W large (quantumExactOutputVector Q large plarge)
            order loop legs test -
          rawOutputDistribution W small (quantumExactOutputVector Q small psmall)
            order loop legs test) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ps, hps, hs⟩ := hsmall
  obtain ⟨_, _, _, _, _, _, _, _, _, pl, hpl, hl⟩ := hlarge
  refine ⟨ps, pl, hps, hpl, ?_⟩
  intro order loop legs test hcompact hnonex
  have hs' := hs order loop legs test hcompact hnonex
  have hl' := hl order loop legs test hcompact hnonex
  linear_combination hl' - hs'

#print axioms liftedOutput_value
#print axioms liftedOutput_corrected
#print axioms recovery_corrected
#print axioms recovery_fixed
#print axioms inactive_weights
#print axioms recovery_exists_iff
#print axioms raw_cutoff_difference
#print axioms recovery_cutoff_difference
end YMYMG.OutputRecovery
