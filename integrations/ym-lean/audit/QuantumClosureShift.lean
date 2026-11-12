import YangMills.QuantumMixingCoordinates

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
A finite change of the actual quantum observable coefficients.
The same generated Q is used throughout. We prove tree normalization,
Ward closure at every loop and the coupling grading; this is not a
construction of a full transformed LocalWardFlowFamily or its limit bridges.
-/
noncomputable section
namespace YMYMG.QuantumShift
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow

variable {G : CompactSimpleGaugeGroup}

def wardMap (Q : QuantumWardLimit G) (g : ℝ) (loop : ℕ)
    (output : LocalMonomial G) : (LocalMonomial G →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun input => Q.coefficient g loop input output)

theorem wardMap_apply (Q : QuantumWardLimit G) (g : ℝ) (loop : ℕ)
    (output : LocalMonomial G) (c : LocalMonomial G →₀ ℂ) :
    wardMap Q g loop output c =
      c.sum (fun input value => value * Q.coefficient g loop input output) := by
  simp [wardMap, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

variable {B : InvariantForm G} {e : ColorFrame B}
  {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
  {lift : QuantumObservableLift G}

/-- Tree closure holds on every admissible output. Filtration supplies
vanishing outside the label's own tested dimension range. -/
theorem tree_closed_all (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p : InvariantInsertionLabel G) (output : LocalMonomial G)
    (ha : output.Admissible) :
    wardMap Q g 0 output (lift.physicalCoefficient g p 0) = 0 := by
  rw [wardMap_apply]
  by_cases hd : output.dimension ≤ intrinsicEngineeringDimension p + 1
  · simpa using h.cocycle g p 0 output ha hd
  · unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro input hi
    have hp := h.physical_support g p 0 input (Finsupp.mem_support_iff.mp hi)
    have hzero : Q.coefficient g 0 input output = 0 := by
      by_contra hn
      have hb := h.ward_filtered g 0 input output hp.1 hn
      omega
    simp only [hzero, mul_zero]

def shiftedOne (lift : QuantumObservableLift G) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) : LocalMonomial G →₀ ℂ :=
  lift.physicalCoefficient g p 1 + ((g : ℂ)^2 * a) • lift.physicalCoefficient g q 0

/-- A finite g² shift by the tree part of another closed physical label
preserves the same generated one-loop Ward equation. -/
theorem one_loop_closed (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) (output : LocalMonomial G)
    (ha : output.Admissible) (hd : output.dimension ≤ intrinsicEngineeringDimension p + 1) :
    wardMap Q g 1 output (lift.physicalCoefficient g p 0) +
      wardMap Q g 0 output (shiftedOne lift g p q a) = 0 := by
  have hc := h.cocycle g p 1 output ha hd
  have hc' : wardMap Q g 1 output (lift.physicalCoefficient g p 0) +
      wardMap Q g 0 output (lift.physicalCoefficient g p 1) = 0 := by
    simpa [wardMap_apply, Fin.sum_univ_succ] using hc
  simp only [shiftedOne, map_add, map_smul, tree_closed_all h g q output ha,
    smul_zero, add_zero]
  exact hc'

theorem shiftedOne_graph_grading (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) (m : LocalMonomial G) :
    shiftedOne lift g p q a m = (g : ℂ)^(m.legs.length + 2) *
      shiftedOne lift 1 p q a m := by
  simp only [shiftedOne, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [h.physical_graph_grading g p 1 m, h.physical_graph_grading g q 0 m]
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Complex.ofReal_one, one_pow, one_mul]
  rw [pow_add]
  ring

theorem shiftedOne_support (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ)
    (hq : intrinsicEngineeringDimension q ≤ intrinsicEngineeringDimension p)
    (m : LocalMonomial G) (hne : shiftedOne lift g p q a m ≠ 0) :
    m.Admissible ∧ m.dimension ≤ intrinsicEngineeringDimension p ∧
      m.ghostNumber = 0 ∧ m.parity = false := by
  by_cases hp : lift.physicalCoefficient g p 1 m ≠ 0
  · exact h.physical_support g p 1 m hp
  · have hq' : lift.physicalCoefficient g q 0 m ≠ 0 := by
      intro hz
      apply hne
      simp [shiftedOne, not_ne_iff.mp hp, hz]
    have hs := h.physical_support g q 0 m hq'
    exact ⟨hs.1, hs.2.1.trans hq, hs.2.2⟩

/-- The same filtration argument extends closure to every loop and every
admissible output, not just the tree term. -/
theorem closed_all (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p : InvariantInsertionLabel G) (loop : ℕ) (output : LocalMonomial G)
    (ha : output.Admissible) :
    (∑ l : Fin (loop+1),
      wardMap Q g (loop-l.val) output (lift.physicalCoefficient g p l.val)) = 0 := by
  simp only [wardMap_apply]
  by_cases hd : output.dimension ≤ intrinsicEngineeringDimension p + 1
  · exact h.cocycle g p loop output ha hd
  · apply Finset.sum_eq_zero
    intro l _
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro input hi
    have hp := h.physical_support g p l.val input (Finsupp.mem_support_iff.mp hi)
    have hzero : Q.coefficient g (loop-l.val) input output = 0 := by
      by_contra hn
      have hb := h.ward_filtered g (loop-l.val) input output hp.1 hn
      omega
    simp only [hzero, mul_zero]

/-- Coefficientwise meaning of O_p -> O_p + hbar*g²*a*O_q. The entire
corrected O_q is used, so closure can be checked at all subsequent loops. -/
def shifted (lift : QuantumObservableLift G) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) : ℕ → LocalMonomial G →₀ ℂ
  | 0 => lift.physicalCoefficient g p 0
  | loop+1 => lift.physicalCoefficient g p (loop+1) +
      ((g : ℂ)^2*a) • lift.physicalCoefficient g q loop

theorem shifted_tree (g : ℝ) (p q : InvariantInsertionLabel G) (a : ℂ) :
    shifted lift g p q a 0 = lift.physicalCoefficient g p 0 := rfl

theorem shifted_closed (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) (loop : ℕ)
    (output : LocalMonomial G) (ha : output.Admissible) :
    (∑ l : Fin (loop+1), wardMap Q g (loop-l.val) output
      (shifted lift g p q a l.val)) = 0 := by
  cases loop with
  | zero => simpa [shifted] using tree_closed_all h g p output ha
  | succ loop =>
    have hp := closed_all h g p (loop+1) output ha
    have hq := closed_all h g q loop output ha
    rw [Fin.sum_univ_succ] at hp ⊢
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right,
      shifted, map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hp ⊢
    rw [hq, mul_zero, add_zero]
    exact hp

theorem shifted_graph_grading (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) (loop : ℕ) (m : LocalMonomial G) :
    shifted lift g p q a loop m = (g : ℂ)^(m.legs.length+2*loop) *
      shifted lift 1 p q a loop m := by
  cases loop with
  | zero => exact h.physical_graph_grading g p 0 m
  | succ loop =>
    simp only [shifted, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [h.physical_graph_grading g p (loop+1) m,
      h.physical_graph_grading g q loop m]
    simp only [Complex.ofReal_one, one_pow, one_mul]
    rw [show m.legs.length+2*(loop+1) = (m.legs.length+2*loop)+2 by omega, pow_add]
    ring

theorem shifted_support (h : lift.Compatible e anomaly Q) (g : ℝ)
    (p q : InvariantInsertionLabel G) (a : ℂ) (loop : ℕ)
    (hq : intrinsicEngineeringDimension q ≤ intrinsicEngineeringDimension p)
    (m : LocalMonomial G) (hne : shifted lift g p q a loop m ≠ 0) :
    m.Admissible ∧ m.dimension ≤ intrinsicEngineeringDimension p ∧
      m.ghostNumber = 0 ∧ m.parity = false := by
  cases loop with
  | zero => exact h.physical_support g p 0 m hne
  | succ loop =>
    by_cases hp : lift.physicalCoefficient g p (loop+1) m ≠ 0
    · exact h.physical_support g p (loop+1) m hp
    · have hq' : lift.physicalCoefficient g q loop m ≠ 0 := by
        intro hz
        apply hne
        simp [shifted, not_ne_iff.mp hp, hz]
      have hs := h.physical_support g q loop m hq'
      exact ⟨hs.1, hs.2.1.trans hq, hs.2.2⟩

#print axioms wardMap_apply
#print axioms tree_closed_all
#print axioms one_loop_closed
#print axioms shiftedOne_graph_grading
#print axioms shiftedOne_support
#print axioms closed_all
#print axioms shifted_tree
#print axioms shifted_closed
#print axioms shifted_graph_grading
#print axioms shifted_support
end YMYMG.QuantumShift
