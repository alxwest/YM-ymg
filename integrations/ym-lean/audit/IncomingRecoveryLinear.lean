import OutputRecoveryCoherent
import IncomingExpansionAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Linear closure of the actual quantum output recovery relation. The
primitive is transformed together with both coefficient vectors. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.IncomingRecovery
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.IncomingExpansion YMYMG.OutputRecoveryExact

theorem vector_delay_apply {I : Type*} (v : ℕ → ℕ → I → ℂ)
    (r l : ℕ) (i : I) : delay v r l i = delay (fun a b => v a b i) r l := by
  obtain r | r | r := r <;> cases l <;> rfl

def sumConvolve {I : Type*} (active : Finset I) (kernel : I → ℕ → ℕ → ℂ) :
    (ℕ → ℕ → I → ℂ) →ₗ[ℂ] (ℕ → ℕ → ℂ) where
  toFun v r l := ∑ i ∈ active, convolve (fun a b => v a b i) (kernel i) r l
  map_add' v w := by
    funext r l
    simp only [Pi.add_apply, convolve_add, Finset.sum_add_distrib]
  map_smul' a v := by
    funext r l
    simp only [Pi.smul_apply, smul_eq_mul, convolve_const_mul, Finset.mul_sum, RingHom.id_apply]

theorem sumConvolve_delay {I : Type*} (active : Finset I) (kernel : I → ℕ → ℕ → ℂ)
    (v : ℕ → ℕ → I → ℂ) :
    sumConvolve active kernel (delay v) = delay (sumConvolve active kernel v) := by
  funext r l
  change (∑ i ∈ active, convolve (fun a b => delay v a b i) (kernel i) r l) = _
  simp only [vector_delay_apply, convolve_delay]
  obtain r | r | r := r <;> cases l <;> simp [delay, sumConvolve]

def matrixConvolve {I J : Type*} (active : Finset I) (kernel : J → I → ℕ → ℕ → ℂ) :
    (ℕ → ℕ → I → ℂ) →ₗ[ℂ] (ℕ → ℕ → J → ℂ) where
  toFun p r l m := sumConvolve active (kernel m) p r l
  map_add' p q := by
    funext r l m
    exact congrFun (congrFun ((sumConvolve active (kernel m)).map_add p q) r) l
  map_smul' a p := by
    funext r l m
    exact congrFun (congrFun ((sumConvolve active (kernel m)).map_smul a p) r) l

theorem matrixConvolve_delay {I J : Type*} (active : Finset I)
    (kernel : J → I → ℕ → ℕ → ℂ) (p : ℕ → ℕ → I → ℂ) :
    matrixConvolve active kernel (delay p) = delay (matrixConvolve active kernel p) := by
  funext r l m
  conv_rhs => rw [vector_delay_apply]
  simp only [matrixConvolve, LinearMap.coe_mk, AddHom.coe_mk, sumConvolve_delay]

theorem support_delay_generic {I : Type*} (allowed : I → Prop)
    (p : ℕ → ℕ → I → ℂ) (hp : ∀ r l i, p r l i ≠ 0 → allowed i) :
    ∀ r l i, delay p r l i ≠ 0 → allowed i := by
  intro r l i hn
  obtain r | r | r := r
  · exact False.elim (hn rfl)
  · exact False.elim (hn rfl)
  · cases l with
    | zero => exact False.elim (hn rfl)
    | succ l => exact hp r l i hn

variable {G : CompactSimpleGaugeGroup}

def rawFunctional (W : WardContinuumData G) (cutoff : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    BigradedMonomialVector G →ₗ[ℂ] (ℕ → ℕ → ℂ) :=
  sumConvolve (monomialsBelow G cutoff)
    (fun m r l => W.physical .single r l (fun _ : Fin 1 => m) legs test)

theorem rawFunctional_apply (W : WardContinuumData G) (cutoff : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (v : BigradedMonomialVector G) (r l : ℕ) :
    rawFunctional W cutoff legs test v r l = rawOutputDistribution W cutoff v r l legs test := by
  simp only [rawFunctional, sumConvolve, convolve, rawOutputDistribution,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk]

def liftedFunctional {n : ℕ} (lift : QuantumObservableLift G) (W : WardContinuumData G)
    (labels : Fin n → InvariantInsertionLabel G) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs) : (ℕ → ℕ → Fin n → ℂ) →ₗ[ℂ] (ℕ → ℕ → ℂ) :=
  sumConvolve Finset.univ (fun i r l => lift.physicalInsertion W (labels i) r l legs test)

theorem liftedFunctional_apply {n : ℕ} (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (labels : Fin n → InvariantInsertionLabel G)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (c : ℕ → ℕ → Fin n → ℂ) (r l : ℕ) :
    liftedFunctional lift W labels legs test c r l =
      liftedOutputDistribution lift W labels c r l legs test := by
  simp only [liftedFunctional, sumConvolve, convolve, liftedOutputDistribution,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def exactMap (Q : QuantumWardLimit G) (cutoff : ℕ) :
    BigradedMonomialVector G →ₗ[ℂ] BigradedMonomialVector G :=
  matrixConvolve (outputPrimitiveMonomials G cutoff)
    (fun output input r l => quantumWardCouplingCoefficient Q r l input output)

theorem exactMap_apply (Q : QuantumWardLimit G) (cutoff : ℕ) (p : BigradedMonomialVector G) :
    exactMap Q cutoff p = quantumExactOutputVector Q cutoff p := by
  funext r l m
  simp only [exactMap, matrixConvolve, sumConvolve, convolve, quantumExactOutputVector,
    LinearMap.coe_mk, AddHom.coe_mk]

theorem rawFunctional_delay (W : WardContinuumData G) (cutoff : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (v : BigradedMonomialVector G) :
    rawFunctional W cutoff legs test (delay v) = delay (rawFunctional W cutoff legs test v) :=
  sumConvolve_delay _ _ v

theorem liftedFunctional_delay {n : ℕ} (lift : QuantumObservableLift G)
    (W : WardContinuumData G) (labels : Fin n → InvariantInsertionLabel G)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs)
    (c : ℕ → ℕ → Fin n → ℂ) :
    liftedFunctional lift W labels legs test (delay c) =
      delay (liftedFunctional lift W labels legs test c) := sumConvolve_delay _ _ c

theorem exactMap_delay (Q : QuantumWardLimit G) (cutoff : ℕ) (p : BigradedMonomialVector G) :
    exactMap Q cutoff (delay p) = delay (exactMap Q cutoff p) := matrixConvolve_delay _ _ p

theorem supported_add {cutoff : ℕ} {p q : BigradedMonomialVector G}
    (hp : SupportedPrimitive cutoff p) (hq : SupportedPrimitive cutoff q) :
    SupportedPrimitive cutoff (p+q) := by
  intro r l m hn
  by_contra hout
  have hp0 : p r l m = 0 := by_contra fun h => hout (hp r l m h)
  have hq0 : q r l m = 0 := by_contra fun h => hout (hq r l m h)
  exact hn (by simp [hp0, hq0])

theorem supported_smul {cutoff : ℕ} {p : BigradedMonomialVector G}
    (hp : SupportedPrimitive cutoff p) (a : ℂ) : SupportedPrimitive cutoff (a • p) := by
  intro r l m hn
  apply hp r l m
  intro hz
  exact hn (by simp [hz])

theorem supported_delay {cutoff : ℕ} {p : BigradedMonomialVector G}
    (hp : SupportedPrimitive cutoff p) : SupportedPrimitive cutoff (delay p) :=
  support_delay_generic (fun m => m ∈ outputPrimitiveMonomials G cutoff) p hp

variable {n : ℕ} {B : InvariantForm G} {e : ColorFrame B}
    {L : ℝ → InsertedFlowFamily G} {transport : SameTheoryWardTransportData e L}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}
    {cutoff : ℕ} {labels : Fin n → InvariantInsertionLabel G}

theorem recovery_add {v w : BigradedMonomialVector G} {c d : ℕ → ℕ → Fin n → ℂ}
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels v c)
    (k : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels w d) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels (v+w) (c+d) := by
  obtain ⟨hc, hl, hw, ha, hf, hn, hs, hd, hg, p, hp, he⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, kg, q, hq, ke⟩ := k
  refine ⟨hc, hl, hw, ha, hf, hn, hs, hd, ?_, p+q, supported_add hp hq, ?_⟩
  · intro r l i hrl
    simp only [Pi.add_apply, hg r l i hrl, kg r l i hrl, add_zero]
  · intro r l legs test hcompact hnonex
    have he' := he r l legs test hcompact hnonex
    have ke' := ke r l legs test hcompact hnonex
    simp only [← rawFunctional_apply, ← liftedFunctional_apply, ← exactMap_apply,
      map_add, Pi.add_apply] at *
    linear_combination he' + ke'

theorem recovery_smul {v : BigradedMonomialVector G} {c : ℕ → ℕ → Fin n → ℂ}
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels v c) (a : ℂ) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels (a • v) (a • c) := by
  obtain ⟨hc, hl, hw, ha, hf, hn, hs, hd, hg, p, hp, he⟩ := h
  refine ⟨hc, hl, hw, ha, hf, hn, hs, hd, ?_, a • p, supported_smul hp a, ?_⟩
  · intro r l i hrl
    simp only [Pi.smul_apply, hg r l i hrl, smul_zero]
  · intro r l legs test hcompact hnonex
    have he' := he r l legs test hcompact hnonex
    simp only [← rawFunctional_apply, ← liftedFunctional_apply, ← exactMap_apply,
      map_smul, Pi.smul_apply, smul_eq_mul] at *
    linear_combination a * he'

theorem recovery_delay {v : BigradedMonomialVector G} {c : ℕ → ℕ → Fin n → ℂ}
    (h : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels v c) :
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff labels (delay v) (delay c) := by
  obtain ⟨hc, hl, hw, ha, hf, hn, hs, hd, hg, p, hp, he⟩ := h
  refine ⟨hc, hl, hw, ha, hf, hn, hs, hd, ?_, delay p, supported_delay hp, ?_⟩
  · intro r l i hrl
    obtain r | r | r := r <;> cases l
    all_goals first | rfl | exact hg _ _ i (by omega)
  · intro r l legs test hcompact hnonex
    simp only [← rawFunctional_apply, ← liftedFunctional_apply, ← exactMap_apply,
      rawFunctional_delay, liftedFunctional_delay, exactMap_delay]
    obtain r | r | r := r <;> cases l
    all_goals simp only [delay, sub_self]
    simpa only [rawFunctional_apply, liftedFunctional_apply, exactMap_apply] using
      he r _ legs test hcompact hnonex

#print axioms vector_delay_apply
#print axioms sumConvolve
#print axioms sumConvolve_delay
#print axioms matrixConvolve
#print axioms matrixConvolve_delay
#print axioms support_delay_generic
#print axioms rawFunctional_apply
#print axioms liftedFunctional_apply
#print axioms exactMap
#print axioms exactMap_apply
#print axioms rawFunctional_delay
#print axioms liftedFunctional_delay
#print axioms exactMap_delay
#print axioms supported_add
#print axioms supported_smul
#print axioms supported_delay
#print axioms recovery_add
#print axioms recovery_smul
#print axioms recovery_delay
end YMYMG.IncomingRecovery
