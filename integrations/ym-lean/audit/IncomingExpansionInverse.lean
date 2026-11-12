import IncomingNativeLimits

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Inverting the entire incoming transformation requires the lower label
to have zero correction weight. This is stronger than checking a single slot. -/
noncomputable section
namespace YMYMG.IncomingExpansion
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.DictionaryRenormalization

theorem expand_weight_zero {I E : Type*} [AddCommGroup E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (lower : I) (n : ℕ) (F : (Fin n → I) → E) (labels : Fin n → I) :
    expandInputs s (fun _ => 0) lower n F labels = F labels := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expandInputs, zero_smul, add_zero, ih, Fin.cons_self_tail]

theorem expand_shift {I E : Type*} [AddCommGroup E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → E) (labels : Fin n → I) :
    expandInputs s w lower n (fun xs => s (F xs)) labels =
      s (expandInputs s w lower n F labels) :=
  (expand_natural s s s (fun _ => rfl) w lower n F labels).symm

/-- The inverse is the same finite tuple transformation with negated
weight, at every arity and with an arbitrary linear order-shift. -/
theorem expand_inverse {I E : Type*} [AddCommGroup E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (hw : w lower = 0)
    (n : ℕ) (F : (Fin n → I) → E) (labels : Fin n → I) :
    expandInputs s (fun p => -w p) lower n
      (fun xs => expandInputs s w lower n F xs) labels = F labels := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expandInputs, Fin.cons_zero, Fin.tail_cons, hw, zero_smul, add_zero]
    rw [expand_add, expand_smul, expand_shift, ih, ih]
    simp only [neg_smul, add_neg_cancel_right, Fin.cons_self_tail]

variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}

theorem regularity_change_iff (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (D : Direction G) (a : ℝ)
    (hq : D.weight D.lower = 0) :
    S.LiftedCoefficientRegularity (change lift D a) ↔ S.LiftedCoefficientRegularity lift := by
  constructor
  · intro h
    simpa only [change_inverse D a hq] using regularity_change S (change lift D a) h D (-a)
  · intro h
    exact regularity_change S lift h D a

#print axioms expand_weight_zero
#print axioms expand_shift
#print axioms expand_inverse
#print axioms regularity_change_iff
end YMYMG.IncomingExpansion
