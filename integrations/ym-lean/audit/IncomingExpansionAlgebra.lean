import WordJetAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Finite multilinear incoming changes, parameterized by their order shift.
The recursion has exactly one binary choice per incoming slot. -/
noncomputable section
namespace YMYMG.IncomingExpansion
open YMYMG.CouplingTaylor YMYMG.WordJet

def expandInputs {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (shift : E →ₗ[ℂ] E) (weight : I → ℂ) (lower : I) :
    (n : ℕ) → ((Fin n → I) → E) → (Fin n → I) → E
  | 0, F, labels => F labels
  | n+1, F, labels =>
      expandInputs shift weight lower n (fun tail => F (Fin.cons (labels 0) tail))
          (Fin.tail labels) +
        weight (labels 0) • shift
          (expandInputs shift weight lower n (fun tail => F (Fin.cons lower tail))
            (Fin.tail labels))

theorem expand_natural {I E F : Type*} [AddCommMonoid E] [Module ℂ E]
    [AddCommMonoid F] [Module ℂ F] (s : E →ₗ[ℂ] E) (t : F →ₗ[ℂ] F)
    (T : E →ₗ[ℂ] F) (hT : ∀ v, T (s v) = t (T v))
    (w : I → ℂ) (lower : I) (n : ℕ) (values : (Fin n → I) → E) (labels : Fin n → I) :
    T (expandInputs s w lower n values labels) =
      expandInputs t w lower n (fun xs => T (values xs)) labels := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expandInputs, map_add, map_smul, hT, ih]

theorem expand_zero {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (n : ℕ) (labels : Fin n → I) :
    expandInputs s w lower n (fun _ => 0) labels = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expandInputs, ih, map_zero, smul_zero, add_zero]

theorem expand_add {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (n : ℕ)
    (F H : (Fin n → I) → E) (labels : Fin n → I) :
    expandInputs s w lower n (fun xs => F xs + H xs) labels =
      expandInputs s w lower n F labels + expandInputs s w lower n H labels := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expandInputs, ih, map_add, smul_add]
    ac_rfl

theorem expand_smul {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (n : ℕ) (a : ℂ)
    (F : (Fin n → I) → E) (labels : Fin n → I) :
    expandInputs s w lower n (fun xs => a • F xs) labels =
      a • expandInputs s w lower n F labels := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expandInputs, ih, map_smul, smul_add]
    rw [smul_comm (w (labels 0)) a]

/-- Finite stability principle; it assumes the property on all old input
tuples, rather than treating a newly generated limit as freely chosen. -/
theorem expand_transfer {I E : Type*} [AddCommMonoid E] [Module ℂ E]
    (s : E →ₗ[ℂ] E) (w : I → ℂ) (lower : I) (P : E → Prop)
    (hadd : ∀ x y, P x → P y → P (x+y))
    (hsmul : ∀ (a : ℂ) x, P x → P (a • x)) (hshift : ∀ x, P x → P (s x))
    (n : ℕ) (F : (Fin n → I) → E) (hF : ∀ labels, P (F labels)) (labels : Fin n → I) :
    P (expandInputs s w lower n F labels) := by
  induction n with
  | zero => exact hF labels
  | succ n ih =>
    apply hadd
    · exact ih _ (fun tail => hF (Fin.cons (labels 0) tail)) _
    · apply hsmul
      apply hshift
      exact ih _ (fun tail => hF (Fin.cons lower tail)) _

def loopDelay {E : Type*} [AddCommMonoid E] [Module ℂ E] :
    (ℕ → E) →ₗ[ℂ] (ℕ → E) where
  toFun F
    | 0 => 0
    | l+1 => F l
  map_add' F H := by funext l; cases l <;> simp
  map_smul' a F := by funext l; cases l <;> simp

theorem loopDelay_zero {E : Type*} [AddCommMonoid E] [Module ℂ E] (F : ℕ → E) :
    loopDelay F 0 = 0 := rfl

theorem loopDelay_succ {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (F : ℕ → E) (loop : ℕ) : loopDelay F (loop+1) = F loop := rfl

def jetDelay {E : Type*} [AddCommMonoid E] [Module ℂ E] :
    (ℕ → ℕ → E) →ₗ[ℂ] (ℕ → ℕ → E) where
  toFun := delay
  map_add' F H := by
    funext order loop
    obtain order | order | order := order <;> cases loop <;> simp [delay]
  map_smul' a F := by
    funext order loop
    obtain order | order | order := order <;> cases loop <;> simp [delay]

theorem jetDelay_apply {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (F : ℕ → ℕ → E) (order loop : ℕ) :
    jetDelay F order loop = delay F order loop := rfl

#print axioms expand_natural
#print axioms expand_zero
#print axioms expand_add
#print axioms expand_smul
#print axioms expand_transfer
#print axioms loopDelay
#print axioms loopDelay_zero
#print axioms loopDelay_succ
#print axioms jetDelay
#print axioms jetDelay_apply
end YMYMG.IncomingExpansion
