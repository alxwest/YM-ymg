import OutputRecoveryExact

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Native low-cutoff obstruction tests, without replacing Q by zero.
All elementary jets have positive engineering dimension. Consequently no
ghost-number -1 primitive is allowed at cutoffs D <= 2. At D = 3 an actual
antighost jet is allowed, so this argument must not be extended blindly. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.OutputRecoveryLowCutoff
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.OutputRecoveryExact

variable {G : CompactSimpleGaugeGroup}

theorem monomial_dimension_zero (m : LocalMonomial G) (hd : m.dimension = 0) : m = 0 := by
  classical
  ext v
  change m v = 0
  by_cases hv : m v = 0
  · exact hv
  · have hmem : v ∈ m.support := Finsupp.mem_support_iff.mpr hv
    have hterm : m v * JetVariable.dimension v ≤ m.dimension := by
      change m v * JetVariable.dimension v ≤ ∑ w ∈ m.support, m w * JetVariable.dimension w
      exact Finset.single_le_sum (f := fun w : JetVariable G => m w * w.dimension)
        (fun _ _ => Nat.zero_le _) hmem
    rw [hd] at hterm
    have hpos := jet_dimension_pos v
    rcases mul_eq_zero.mp (Nat.eq_zero_of_le_zero hterm) with hm | hj
    · exact hm
    · omega

theorem primitiveSet_empty (cutoff : ℕ) (hcutoff : cutoff ≤ 2) :
    outputPrimitiveMonomials G cutoff = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro m hm
  obtain ⟨_, hd, hg, _⟩ := Finset.mem_filter.mp hm
  have hz : m = 0 := monomial_dimension_zero m (by omega)
  subst m
  simp [LocalMonomial.ghostNumber] at hg

theorem supportedPrimitive_zero (cutoff : ℕ) (hcutoff : cutoff ≤ 2)
    (p : BigradedMonomialVector G) (hp : SupportedPrimitive cutoff p) : p = 0 := by
  funext order loop m
  by_contra hn
  have hm := hp order loop m hn
  rw [primitiveSet_empty cutoff hcutoff] at hm
  simp only [Finset.notMem_empty] at hm

theorem quantumExact_low_zero (Q : QuantumWardLimit G) (cutoff : ℕ)
    (hcutoff : cutoff ≤ 2) (p : BigradedMonomialVector G) :
    quantumExactOutputVector Q cutoff p = 0 := by
  funext order loop output
  simp [quantumExactOutputVector, primitiveSet_empty cutoff hcutoff]

/-- No smoothness, nilpotence, Ward quotient or vanishing assumption on Q
is needed: the primitive sum itself is empty. -/
theorem exactOutput_low_zero (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (cutoff : ℕ) (hcutoff : cutoff ≤ 2) (p : BigradedMonomialVector G)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    exactOutput W Q cutoff p order loop legs test = 0 := by
  simp [exactOutput, quantumExact_low_zero Q cutoff hcutoff, rawOutputDistribution]

variable {n : ℕ} {B : InvariantForm G} {e : ColorFrame B}
    {L : ℝ → InsertedFlowFamily G} {transport : SameTheoryWardTransportData e L}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}

theorem exact_change_iff_equal_outputs (cutoff : ℕ) (hcutoff : cutoff ≤ 2)
    (labels : Fin n → InvariantInsertionLabel G)
    (old proposed : ℕ → ℕ → Fin n → ℂ) :
    CoefficientChangeExact lift W Q cutoff labels old proposed ↔
      ∀ order loop legs (test : JointMomentumTest 1 legs),
        HasCompactSupport test → NonexceptionalSupport .single test →
        liftedOutputDistribution lift W labels proposed order loop legs test =
          liftedOutputDistribution lift W labels old order loop legs test := by
  constructor
  · rintro ⟨p, _, he⟩ order loop legs test hcompact hnonex
    have h := he order loop legs test hcompact hnonex
    rw [exactOutput_low_zero W Q cutoff hcutoff] at h
    exact sub_eq_zero.mp h
  · intro he
    refine ⟨0, supported_zero cutoff, ?_⟩
    intro order loop legs test hcompact hnonex
    rw [he order loop legs test hcompact hnonex, sub_self, exactOutput_zero]

/-- Every native recovery at D <= 2 is a literal equality of distributions
on the native compact nonexceptional tests. Coefficient injectivity is not
assumed and does not follow from this result. -/
theorem recovery_low_equation (cutoff : ℕ) (hcutoff : cutoff ≤ 2)
    (labels : Fin n → InvariantInsertionLabel G) (raw : BigradedMonomialVector G)
    (c : ℕ → ℕ → Fin n → ℂ)
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw c)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (hcompact : HasCompactSupport test) (hnonex : NonexceptionalSupport .single test) :
    rawOutputDistribution W cutoff raw order loop legs test =
      liftedOutputDistribution lift W labels c order loop legs test := by
  obtain ⟨_, _, _, _, _, _, _, _, _, p, _, he⟩ := h
  have hzero := exactOutput_low_zero W Q cutoff hcutoff p order loop legs test
  have hh := he order loop legs test hcompact hnonex
  simp only [exactOutput] at hzero
  rw [hzero] at hh
  exact sub_eq_zero.mp hh

theorem recovery_low_iff (cutoff : ℕ) (hcutoff : cutoff ≤ 2)
    (labels : Fin n → InvariantInsertionLabel G) (raw : BigradedMonomialVector G)
    (old proposed : ℕ → ℕ → Fin n → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw old)
    (hgraph : ∀ order loop i, order < 2*loop → proposed order loop i = 0) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw proposed ↔
      ∀ order loop legs (test : JointMomentumTest 1 legs),
        HasCompactSupport test → NonexceptionalSupport .single test →
        liftedOutputDistribution lift W labels proposed order loop legs test =
          liftedOutputDistribution lift W labels old order loop legs test := by
  rw [recovery_iff_exact cutoff labels raw old proposed hold hgraph,
    exact_change_iff_equal_outputs cutoff hcutoff]

/-- At these native cutoffs a nonzero difference on just one allowed test
cannot be repaired by any permitted generated-Q primitive. -/
theorem no_low_recovery (cutoff : ℕ) (hcutoff : cutoff ≤ 2)
    (labels : Fin n → InvariantInsertionLabel G) (raw : BigradedMonomialVector G)
    (old proposed : ℕ → ℕ → Fin n → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw old)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (hcompact : HasCompactSupport test) (hnonex : NonexceptionalSupport .single test)
    (hseparate : liftedOutputDistribution lift W labels proposed order loop legs test ≠
      liftedOutputDistribution lift W labels old order loop legs test) :
    ¬ QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels raw proposed := by
  intro hnew
  have h0 := recovery_low_equation cutoff hcutoff labels raw old hold
    order loop legs test hcompact hnonex
  have h1 := recovery_low_equation cutoff hcutoff labels raw proposed hnew
    order loop legs test hcompact hnonex
  exact hseparate (h1.symm.trans h0)

def antighostMonomial (a : Fin G.dimension) : LocalMonomial G :=
  Finsupp.single (Sum.inl (BasicField.antighost a), 0) 1

/-- Sharpness control: an actual ghost-number -1, odd, degree-one native
monomial is admitted at cutoff three. A color index is explicit. -/
theorem antighost_primitive_at_three (a : Fin G.dimension) :
    antighostMonomial a ∈ outputPrimitiveMonomials G 3 := by
  classical
  have ha : (antighostMonomial a).Admissible := by
    intro v _
    simp only [antighostMonomial, Finsupp.single_apply]
    split_ifs <;> omega
  have hd : (antighostMonomial a).dimension = 1 := by
    simp [antighostMonomial, LocalMonomial.dimension, JetVariable.dimension,
      ExternalLeg.dimension, BasicField.dimension]
  have hg : (antighostMonomial a).ghostNumber = -1 := by
    simp [antighostMonomial, LocalMonomial.ghostNumber, ExternalLeg.ghostNumber,
      basicGhostNumber]
  have hp : (antighostMonomial a).parity = true := by
    simp [antighostMonomial, LocalMonomial.parity, LocalMonomial.oddMultiplicity,
      ExternalLeg.parity, BasicField.fermionic]
  exact Finset.mem_filter.mpr ⟨(mem_monomialsBelow_iff 3 _).mpr ⟨ha, by omega⟩,
    by omega, hg, hp⟩

#print axioms monomial_dimension_zero
#print axioms primitiveSet_empty
#print axioms supportedPrimitive_zero
#print axioms quantumExact_low_zero
#print axioms exactOutput_low_zero
#print axioms exact_change_iff_equal_outputs
#print axioms recovery_low_equation
#print axioms recovery_low_iff
#print axioms no_low_recovery
#print axioms antighost_primitive_at_three
end YMYMG.OutputRecoveryLowCutoff
