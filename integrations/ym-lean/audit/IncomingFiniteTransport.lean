import IncomingExpansionAlgebra
import DictionaryInsertionTransport
import YangMills.LiftedCompositeExtraction
import YangMills.GeneratedEuclideanCoefficients

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Exact incoming transport through the native finite regulated extractor.
The raw insertion functional is arbitrary here, so the result applies to
the actual recursive OPE construction without changing that construction. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.IncomingExpansion
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.DictionaryRenormalization

variable {G : CompactSimpleGaugeGroup}
abbrev FiniteState (G : CompactSimpleGaugeGroup) := ℕ → List (PositionedInsertion G) → ℂ

def coefficientFunctional (F : FiniteState G) (x : Spacetime)
    (loop : ℕ) (acc : List (PositionedInsertion G)) : (LocalMonomial G →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun m => F loop (acc ++ [⟨m,x⟩]))

theorem coefficientFunctional_apply (F : FiniteState G) (x : Spacetime)
    (loop : ℕ) (acc : List (PositionedInsertion G)) (c : LocalMonomial G →₀ ℂ) :
    coefficientFunctional F x loop acc c = c.sum (fun m a => a * F loop (acc ++ [⟨m,x⟩])) := by
  simp [coefficientFunctional, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

def finiteSlot (lift : QuantumObservableLift G) (g UV : ℝ)
    (p : InvariantInsertionLabel G) (x : Spacetime) : FiniteState G →ₗ[ℂ] FiniteState G where
  toFun F loop acc := ∑ l : Fin (loop+1), (lift.coefficient g p l.val UV).sum
    (fun m c => c * F (loop-l.val) (acc ++ [⟨m,x⟩]))
  map_add' F H := by
    funext loop acc
    simp only [Pi.add_apply, mul_add, Finsupp.sum, Finset.sum_add_distrib]
  map_smul' a F := by
    funext loop acc
    simp only [Pi.smul_apply, smul_eq_mul, Finsupp.sum, mul_left_comm,
      Finset.mul_sum, RingHom.id_apply]

theorem finiteSlot_apply (lift : QuantumObservableLift G) (g UV : ℝ)
    (p : InvariantInsertionLabel G) (x : Spacetime) (F : FiniteState G)
    (loop : ℕ) (acc : List (PositionedInsertion G)) :
    finiteSlot lift g UV p x F loop acc = ∑ l : Fin (loop+1),
      (lift.coefficient g p l.val UV).sum
        (fun m c => c * F (loop-l.val) (acc ++ [⟨m,x⟩])) := rfl

theorem finiteSlot_delay (lift : QuantumObservableLift G) (g UV : ℝ)
    (p : InvariantInsertionLabel G) (x : Spacetime) (F : FiniteState G) :
    finiteSlot lift g UV p x (loopDelay F) = loopDelay (finiteSlot lift g UV p x F) := by
  funext loop acc
  cases loop with
  | zero => simp [finiteSlot_apply, loopDelay_zero]
  | succ loop =>
    rw [loopDelay_succ]
    simp only [finiteSlot_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, loopDelay_zero,
      Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero, add_zero]
    apply Finset.sum_congr rfl
    intro l _
    have hd : loop+1-l.val = (loop-l.val)+1 := by omega
    rw [hd, loopDelay_succ]

theorem finiteSlot_change (lift : QuantumObservableLift G) (D : Direction G)
    (a g UV : ℝ) (p : InvariantInsertionLabel G) (x : Spacetime) (F : FiniteState G) :
    finiteSlot (change lift D a) g UV p x F = finiteSlot lift g UV p x F +
      ((g : ℂ)^2 * ((a * D.weight p : ℝ) : ℂ)) •
        loopDelay (finiteSlot lift g UV D.lower x F) := by
  funext loop acc
  cases loop with
  | zero => simp [finiteSlot_apply, change, loopDelay_zero]
  | succ loop =>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, loopDelay_succ,
      finiteSlot_apply, ← coefficientFunctional_apply]
    conv_lhs => rw [Fin.sum_univ_succ]
    conv_rhs => lhs; rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right,
      change, map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

def finiteWord (lift : QuantumObservableLift G) (g UV : ℝ) :
    {n : ℕ} → (Fin n → Spacetime) → (Fin n → InvariantInsertionLabel G) →
      FiniteState G →ₗ[ℂ] FiniteState G
  | 0, _, _ => LinearMap.id
  | _+1, positions, labels =>
      (finiteSlot lift g UV (labels 0) (positions 0)).comp
        (finiteWord lift g UV (Fin.tail positions) (Fin.tail labels))

theorem finiteWord_delay (lift : QuantumObservableLift G) (g UV : ℝ) (n : ℕ)
    (positions : Fin n → Spacetime) (labels : Fin n → InvariantInsertionLabel G)
    (F : FiniteState G) :
    finiteWord lift g UV positions labels (loopDelay F) =
      loopDelay (finiteWord lift g UV positions labels F) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteWord, LinearMap.comp_apply, ih, finiteSlot_delay]

theorem finiteWord_native (lift : QuantumObservableLift G) (g UV : ℝ) (n : ℕ)
    (positions : Fin n → Spacetime) (labels : Fin n → InvariantInsertionLabel G)
    (F : FiniteState G) (loop : ℕ) (acc : List (PositionedInsertion G)) :
    finiteWord lift g UV positions labels F loop acc =
      liftedInsertionExpansion lift g UV F (List.ofFn fun i => (labels i,positions i)) loop acc := by
  induction n generalizing loop acc with
  | zero => simp [finiteWord, liftedInsertionExpansion]
  | succ n ih =>
    simp only [finiteWord, LinearMap.comp_apply, finiteSlot_apply,
      List.ofFn_succ, liftedInsertionExpansion, ih, Fin.tail_def]

theorem finiteWord_change {I : Type*} (lift : QuantumObservableLift G) (D : Direction G)
    (decode : I → InvariantInsertionLabel G) (lower : I) (hlower : decode lower = D.lower)
    (a g UV : ℝ) (n : ℕ) (positions : Fin n → Spacetime) (labels : Fin n → I)
    (F : FiniteState G) :
    finiteWord (change lift D a) g UV positions (fun i => decode (labels i)) F =
      expandInputs loopDelay (fun p => (g : ℂ)^2 * ((a * D.weight (decode p) : ℝ) : ℂ))
        lower n (fun xs => finiteWord lift g UV positions (fun i => decode (xs i)) F) labels := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finiteWord, LinearMap.comp_apply]
    rw [finiteSlot_change]
    have htail := ih (Fin.tail positions) (Fin.tail labels)
    simp only [Fin.tail_def] at htail ⊢
    rw [htail]
    rw [expand_natural loopDelay loopDelay (finiteSlot lift g UV (decode (labels 0)) (positions 0))
      (finiteSlot_delay lift g UV (decode (labels 0)) (positions 0))]
    rw [expand_natural loopDelay loopDelay (finiteSlot lift g UV D.lower (positions 0))
      (finiteSlot_delay lift g UV D.lower (positions 0))]
    simp only [expandInputs, Fin.cons_zero, Fin.cons_succ, Fin.tail_def, hlower]

#print axioms coefficientFunctional_apply
#print axioms finiteSlot
#print axioms finiteSlot_apply
#print axioms finiteSlot_delay
#print axioms finiteSlot_change
#print axioms finiteWord_delay
#print axioms finiteWord_native
#print axioms finiteWord_change
end YMYMG.IncomingExpansion
