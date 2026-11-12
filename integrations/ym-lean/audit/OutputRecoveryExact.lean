import OutputRecoveryTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! An exact criterion for changing physical recovery coefficients.
The range below is that of the actual native generated Q on the actual
cutoff-supported primitives, with the original admissible test class.
No vanishing of Q-exact insertions or quantum-field independence is assumed. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.OutputRecoveryExact
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.DictionaryRenormalization YMYMG.OutputRecovery

variable {G : CompactSimpleGaugeGroup}

def SupportedPrimitive (cutoff : ℕ) (p : BigradedMonomialVector G) : Prop :=
  ∀ order loop m, p order loop m ≠ 0 → m ∈ outputPrimitiveMonomials G cutoff

def exactOutput (W : WardContinuumData G) (Q : QuantumWardLimit G) (cutoff : ℕ)
    (p : BigradedMonomialVector G) (order loop : ℕ) (legs : List (ExternalLeg G)) :
    JointMomentumDistribution 1 legs :=
  rawOutputDistribution W cutoff (quantumExactOutputVector Q cutoff p) order loop legs

theorem supported_zero (cutoff : ℕ) :
    SupportedPrimitive (G := G) cutoff 0 := by
  intro order loop m hm
  exact False.elim (hm rfl)

theorem supported_sub {cutoff : ℕ} {p q : BigradedMonomialVector G}
    (hp : SupportedPrimitive cutoff p) (hq : SupportedPrimitive cutoff q) :
    SupportedPrimitive cutoff (p-q) := by
  intro order loop m hn
  by_contra hout
  have hp0 : p order loop m = 0 := by_contra fun h => hout (hp order loop m h)
  have hq0 : q order loop m = 0 := by_contra fun h => hout (hq order loop m h)
  exact hn (by simp [hp0, hq0])

theorem quantumExact_sub (Q : QuantumWardLimit G) (cutoff : ℕ)
    (p q : BigradedMonomialVector G) :
    quantumExactOutputVector Q cutoff (p-q) =
      quantumExactOutputVector Q cutoff p - quantumExactOutputVector Q cutoff q := by
  funext order loop output
  simp only [quantumExactOutputVector, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem rawOutput_sub (W : WardContinuumData G) (cutoff : ℕ)
    (p q : BigradedMonomialVector G) (order loop : ℕ) (legs : List (ExternalLeg G)) :
    rawOutputDistribution W cutoff (p-q) order loop legs =
      rawOutputDistribution W cutoff p order loop legs -
        rawOutputDistribution W cutoff q order loop legs := by
  simp only [rawOutputDistribution, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem exactOutput_sub (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (cutoff : ℕ) (p q : BigradedMonomialVector G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    exactOutput W Q cutoff (p-q) order loop legs test =
      exactOutput W Q cutoff p order loop legs test -
        exactOutput W Q cutoff q order loop legs test := by
  simp only [exactOutput, quantumExact_sub, rawOutput_sub, LinearMap.sub_apply]

theorem exactOutput_zero (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (cutoff order loop : ℕ) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs) :
    exactOutput W Q cutoff 0 order loop legs test = 0 := by
  simp [exactOutput, rawOutputDistribution, quantumExactOutputVector]

/-- Difference of the two outgoing assemblies lies in the actual native
generated-Q image, with one supported primitive working on every test. -/
def CoefficientChangeExact {n : ℕ} (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (Q : QuantumWardLimit G) (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G)
    (old proposed : ℕ → ℕ → Fin n → ℂ) : Prop :=
  ∃ p : BigradedMonomialVector G, SupportedPrimitive cutoff p ∧
    ∀ order loop legs (test : JointMomentumTest 1 legs),
      HasCompactSupport test → NonexceptionalSupport .single test →
      liftedOutputDistribution lift W labels proposed order loop legs test -
        liftedOutputDistribution lift W labels old order loop legs test =
          exactOutput W Q cutoff p order loop legs test

variable {n : ℕ} {B : InvariantForm G} {e : ColorFrame B}
    {L : ℝ → InsertedFlowFamily G} {transport : SameTheoryWardTransportData e L}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}

/-- Necessary and sufficient, not merely a sufficient transport recipe.
When the difference equals Q(h), the new recovery primitive is p-h. -/
theorem recovery_iff_exact (cutoff : ℕ) (labels : Fin n → InvariantInsertionLabel G)
    (raw : BigradedMonomialVector G) (old proposed : ℕ → ℕ → Fin n → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw old)
    (hgraph : ∀ order loop i, order < 2*loop → proposed order loop i = 0) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw proposed ↔
      CoefficientChangeExact lift W Q cutoff labels old proposed := by
  obtain ⟨hc, hl, hw, ha, hf, hn, hs, hd, _, p, hp, he⟩ := hold
  constructor
  · intro hnew
    obtain ⟨_, _, _, _, _, _, _, _, _, q, hq, hnewEq⟩ := hnew
    refine ⟨p-q, supported_sub hp hq, ?_⟩
    intro order loop legs test hcompact hnonex
    rw [exactOutput_sub]
    have he' := he order loop legs test hcompact hnonex
    have hn' := hnewEq order loop legs test hcompact hnonex
    simp only [exactOutput]
    linear_combination he' - hn'
  · rintro ⟨q, hq, hqeq⟩
    refine ⟨hc, hl, hw, ha, hf, hn, hs, hd, hgraph, p-q, supported_sub hp hq, ?_⟩
    intro order loop legs test hcompact hnonex
    rw [quantumExact_sub, rawOutput_sub, LinearMap.sub_apply]
    have he' := he order loop legs test hcompact hnonex
    have hq' := hqeq order loop legs test hcompact hnonex
    simp only [exactOutput] at hq'
    linear_combination he' - hq'

/-- Native recovery does not require equality of coefficient tables if
their actual outgoing distributions agree on all admissible tests. -/
theorem recovery_of_equal_outputs (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G) (raw : BigradedMonomialVector G)
    (old proposed : ℕ → ℕ → Fin n → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw old)
    (hgraph : ∀ order loop i, order < 2*loop → proposed order loop i = 0)
    (heq : ∀ order loop legs (test : JointMomentumTest 1 legs),
      HasCompactSupport test → NonexceptionalSupport .single test →
      liftedOutputDistribution lift W labels proposed order loop legs test =
        liftedOutputDistribution lift W labels old order loop legs test) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw proposed := by
  apply (recovery_iff_exact cutoff labels raw old proposed hold hgraph).mpr
  refine ⟨0, supported_zero cutoff, ?_⟩
  intro order loop legs test hcompact hnonex
  rw [heq order loop legs test hcompact hnonex, sub_self, exactOutput_zero]

/-- Apply the exact criterion after the previously proved dictionary
transport. A proposed common coefficient table need not equal the explicit
cutoff-dependent inverse table if their discrepancy is generated-Q exact. -/
theorem corrected_recovery_iff_exact (D : Direction G) (hq : D.weight D.lower = 0)
    (a : ℝ) (cutoff : ℕ) (labels : Fin n → InvariantInsertionLabel G)
    (k : Fin n) (hk : labels k = D.lower) (raw : BigradedMonomialVector G)
    (old proposed : ℕ → ℕ → Fin n → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw old)
    (hgraph : ∀ order loop i, order < 2*loop → proposed order loop i = 0) :
    QuantumPhysicalOutputRecovery e L transport (change lift D a) W Q
      cutoff labels raw proposed ↔
    CoefficientChangeExact (change lift D a) W Q cutoff labels
      (corrected (fun i => D.weight (labels i)) k a old) proposed :=
  recovery_iff_exact cutoff labels raw _ proposed
    (recovery_corrected D hq a cutoff labels k hk raw old hold) hgraph

/-- A single admissible test separating the proposed outputs from the
native Q-image rules out recovery. The annihilation hypothesis concerns
every permitted primitive, not just the primitive of one old witness. -/
theorem no_recovery_of_separating_test (cutoff : ℕ)
    (labels : Fin n → InvariantInsertionLabel G) (raw : BigradedMonomialVector G)
    (old proposed : ℕ → ℕ → Fin n → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw old)
    (hgraph : ∀ order loop i, order < 2*loop → proposed order loop i = 0)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (hcompact : HasCompactSupport test) (hnonex : NonexceptionalSupport .single test)
    (hkill : ∀ p : BigradedMonomialVector G, SupportedPrimitive cutoff p →
      exactOutput W Q cutoff p order loop legs test = 0)
    (hseparate : liftedOutputDistribution lift W labels proposed order loop legs test ≠
      liftedOutputDistribution lift W labels old order loop legs test) :
    ¬ QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw proposed := by
  intro hnew
  obtain ⟨p, hp, he⟩ := (recovery_iff_exact cutoff labels raw old proposed hold hgraph).mp hnew
  have hd := he order loop legs test hcompact hnonex
  rw [hkill p hp] at hd
  exact hseparate (sub_eq_zero.mp hd)

#print axioms supported_zero
#print axioms supported_sub
#print axioms quantumExact_sub
#print axioms rawOutput_sub
#print axioms exactOutput_sub
#print axioms exactOutput_zero
#print axioms recovery_iff_exact
#print axioms recovery_of_equal_outputs
#print axioms corrected_recovery_iff_exact
#print axioms no_recovery_of_separating_test
end YMYMG.OutputRecoveryExact
