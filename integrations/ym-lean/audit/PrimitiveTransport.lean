import ExactInsertionSmoothness

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! The quantum-exact primitive for the same elementary dictionary change.
Its coefficients, support, smoothness and graph power are constructed in
the native type before transporting its actual generated-Q insertion. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.ExactTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre
open YMYMG.DictionaryRenormalization YMYMG.CouplingTaylor
open YMYMG.LegendreTransport
variable {G : CompactSimpleGaugeGroup}

def primitiveCoefficients
    (P : (p : InvariantInsertionLabel G) → LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (D : Direction G) (a : ℝ → ℝ) (p : InvariantInsertionLabel G) (mu g : ℝ) :
    ℕ → LocalMonomial G →₀ ℂ
  | 0 => (P p).coefficient mu g 0
  | loop+1 => (P p).coefficient mu g (loop+1) +
      ((g : ℂ)^2 * (a mu*D.weight p : ℝ)) • (P D.lower).coefficient mu g loop

def changePrimitive
    (P : (p : InvariantInsertionLabel G) → LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (D : Direction G) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (p : InvariantInsertionLabel G) : LocalScalePrimitive G (intrinsicEngineeringDimension p) 0 where
  coefficient := primitiveCoefficients P D a p
  support mu g loop m hn := by
    cases loop with
    | zero => exact (P p).support mu g 0 m hn
    | succ loop =>
      by_cases hp : (P p).coefficient mu g (loop+1) m ≠ 0
      · exact (P p).support mu g (loop+1) m hp
      · have hw : D.weight p ≠ 0 := by
          intro hz
          apply hn
          simp [primitiveCoefficients, hz, not_ne_iff.mp hp]
        have hq : (P D.lower).coefficient mu g loop m ≠ 0 := by
          intro hz
          apply hn
          simp [primitiveCoefficients, Finsupp.add_apply, Finsupp.smul_apply,
            hz, not_ne_iff.mp hp]
        have hh := (P D.lower).support mu g loop m hq
        exact ⟨hh.1, hh.2.1.trans (D.filtered p hw), hh.2.2⟩
  smooth loop m := by
    cases loop with
    | zero => exact (P p).smooth 0 m
    | succ loop =>
      have has : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => a z.1) (Set.Ioi 0 ×ˢ Set.univ) :=
        ha.comp contDiffOn_fst (fun z hz => hz.1)
      have hg : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (z.2 : ℂ)^2)
          (Set.Ioi 0 ×ˢ Set.univ) :=
        (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).pow 2
      have hw := Complex.ofRealCLM.contDiff.comp_contDiffOn
        (has.mul (contDiffOn_const (c := D.weight p)))
      exact ((P p).smooth (loop+1) m).add ((hg.mul hw).mul ((P D.lower).smooth loop m))
  classical mu g hmu := (P p).classical mu g hmu
  graph_power mu g loop m := by
    cases loop with
    | zero => exact (P p).graph_power mu g 0 m
    | succ loop =>
      simp only [primitiveCoefficients, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        Nat.zero_le, if_true, Nat.sub_zero, Complex.ofReal_one, one_pow, one_mul]
      rw [(P p).graph_power mu g (loop+1) m, (P D.lower).graph_power mu g loop m]
      simp only [Nat.zero_le, if_true, Nat.sub_zero]
      rw [show m.legs.length+2*(loop+1) = (m.legs.length+2*loop)+2 by omega, pow_add]
      ring

def exactFunctional {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (anomaly : LocalAnomalyCoefficients G) (L : InsertedFlowFamily G)
    (x : Spacetime) (loop : ℕ) (IR UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : (LocalMonomial G →₀ ℂ) →ₗ[ℂ] ℂ :=
  ∑ b : Fin (loop+1), Finsupp.linearCombination ℂ (fun input =>
    ∑ output ∈ monomialsBelow G (input.dimension+2),
      generatedQuantumWardCoefficient e g anomaly b.val UV input output *
        L [⟨output,x⟩] (loop-b.val) IR UV legs q)

theorem exactFunctional_apply {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (anomaly : LocalAnomalyCoefficients G) (L : InsertedFlowFamily G)
    (x : Spacetime) (loop : ℕ) (IR UV : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (c : LocalMonomial G →₀ ℂ) :
    exactFunctional e g anomaly L x loop IR UV legs q c =
      ∑ b : Fin (loop+1), c.sum (fun input v =>
        ∑ output ∈ monomialsBelow G (input.dimension+2),
          v * generatedQuantumWardCoefficient e g anomaly b.val UV input output *
            L [⟨output,x⟩] (loop-b.val) IR UV legs q) := by
  simp only [exactFunctional, LinearMap.sum_apply, Finsupp.linearCombination_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem exactInsertion_functional {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (L : ℝ → ℝ → InsertedFlowFamily G)
    {degree offset : ℕ} (P : LocalScalePrimitive G degree offset)
    (mu g : ℝ) (x : Spacetime) (loop : ℕ) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    quantumExactInsertion e anomaly L P mu g x loop IR UV legs q =
      ∑ a : Fin (loop+1), exactFunctional e g (anomaly mu g) (L mu g) x
        (loop-a.val) IR UV legs q (P.coefficient mu g a.val) := by
  simp only [quantumExactInsertion, exactFunctional_apply]

theorem exactInsertion_change_zero {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (P : (p : InvariantInsertionLabel G) → LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (D : Direction G) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (p : InvariantInsertionLabel G) (mu g : ℝ) (x : Spacetime) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    quantumExactInsertion e anomaly L (changePrimitive P D a ha p) mu g x 0 IR UV legs q =
      quantumExactInsertion e anomaly L (P p) mu g x 0 IR UV legs q := by
  simp [exactInsertion_functional, changePrimitive, primitiveCoefficients]

theorem exactInsertion_change_succ {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (L : ℝ → ℝ → InsertedFlowFamily G)
    (P : (p : InvariantInsertionLabel G) → LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (D : Direction G) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (p : InvariantInsertionLabel G) (mu g : ℝ) (x : Spacetime) (loop : ℕ) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    quantumExactInsertion e anomaly L (changePrimitive P D a ha p) mu g x (loop+1) IR UV legs q =
      quantumExactInsertion e anomaly L (P p) mu g x (loop+1) IR UV legs q +
      ((g : ℂ)^2 * (a mu*D.weight p : ℝ)) *
        quantumExactInsertion e anomaly L (P D.lower) mu g x loop IR UV legs q := by
  simp only [exactInsertion_functional]
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => lhs; rw [Fin.sum_univ_succ]
  simp only [changePrimitive, primitiveCoefficients, Fin.val_zero, Nat.sub_zero,
    Fin.val_succ, Nat.add_sub_add_right, map_add, map_smul, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

#print axioms changePrimitive
#print axioms exactFunctional_apply
#print axioms exactInsertion_functional
#print axioms exactInsertion_change_zero
#print axioms exactInsertion_change_succ
end YMYMG.ExactTransport
