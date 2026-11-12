import IncomingExpansionAlgebra
import YangMills.GeneratedEuclideanCoefficients

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Finite sums, integration and weak limits for the incoming expansion.
No exchange of an infinite series and a limit is used. -/
noncomputable section
open MeasureTheory Filter
namespace YMYMG.IncomingExpansion
open YMYMG.CouplingTaylor

theorem expand_integrable {I X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : I → ℂ) (lower : I) (n : ℕ) (F : (Fin n → I) → X → ℕ → ℕ → ℂ)
    (hF : ∀ xs r l, Integrable (fun x => F xs x r l) μ)
    (labels : Fin n → I) (order loop : ℕ) :
    Integrable (fun x => expandInputs jetDelay w lower n (fun xs => F xs x)
      labels order loop) μ := by
  induction n generalizing order loop with
  | zero => exact hF labels order loop
  | succ n ih =>
    simp only [expandInputs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jetDelay_apply]
    apply Integrable.add (ih _ (fun xs r l => hF (Fin.cons (labels 0) xs) r l) _ _ _)
    obtain order | order | order := order <;> cases loop
    all_goals simp only [delay, mul_zero]
    all_goals first
      | exact integrable_zero _ _ _
      | exact (ih _ (fun xs r l => hF (Fin.cons lower xs) r l) _ _ _).const_mul _

theorem expand_integral {I X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : I → ℂ) (lower : I) (n : ℕ) (F : (Fin n → I) → X → ℕ → ℕ → ℂ)
    (hF : ∀ xs r l, Integrable (fun x => F xs x r l) μ)
    (labels : Fin n → I) (order loop : ℕ) :
    (∫ x, expandInputs jetDelay w lower n (fun xs => F xs x) labels order loop ∂μ) =
      expandInputs jetDelay w lower n (fun xs r l => ∫ x, F xs x r l ∂μ) labels order loop := by
  induction n generalizing order loop with
  | zero => rfl
  | succ n ih =>
    have hp := expand_integrable μ w lower n (fun xs => F (Fin.cons (labels 0) xs))
      (fun xs r l => hF (Fin.cons (labels 0) xs) r l) (Fin.tail labels)
    have hq := expand_integrable μ w lower n (fun xs => F (Fin.cons lower xs))
      (fun xs r l => hF (Fin.cons lower xs) r l) (Fin.tail labels)
    simp only [expandInputs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jetDelay_apply]
    have hi : Integrable (fun x => w (labels 0) * delay
        (expandInputs jetDelay w lower n (fun xs => F (Fin.cons lower xs) x)
          (Fin.tail labels)) order loop) μ := by
      obtain order | order | order := order <;> cases loop
      all_goals simp only [delay, mul_zero]
      all_goals first | exact integrable_zero _ _ _ | exact (hq _ _).const_mul _
    rw [integral_add (hp order loop) hi,
      ih _ (fun xs r l => hF (Fin.cons (labels 0) xs) r l)]
    rw [integral_const_mul]
    obtain order | order | order := order <;> cases loop
    all_goals simp only [delay, integral_zero]
    exact congrArg (fun z => _ + w (labels 0) * z)
      (ih _ (fun xs r l => hF (Fin.cons lower xs) r l) _ _ _)

theorem expand_tendsto {I X : Type*} {filter : Filter X}
    (w : I → ℂ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → X → ℕ → ℕ → ℂ) (limit : (Fin n → I) → ℕ → ℕ → ℂ)
    (hF : ∀ xs r l, Tendsto (fun x => F xs x r l) filter (nhds (limit xs r l)))
    (labels : Fin n → I) (order loop : ℕ) :
    Tendsto (fun x => expandInputs jetDelay w lower n (fun xs => F xs x) labels order loop)
      filter (nhds (expandInputs jetDelay w lower n limit labels order loop)) := by
  induction n generalizing order loop with
  | zero => exact hF labels order loop
  | succ n ih =>
    simp only [expandInputs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jetDelay_apply]
    apply Tendsto.add (ih _ _ (fun xs r l => hF (Fin.cons (labels 0) xs) r l) _ _ _)
    apply Tendsto.const_mul
    exact delay_tendsto _ _
      (ih _ _ (fun xs r l => hF (Fin.cons lower xs) r l) (Fin.tail labels)) order loop

/-- A fixed spatial multiplier commutes with the finite order expansion. -/
theorem expand_mul {I : Type*} (w : I → ℂ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → ℕ → ℕ → ℂ) (labels : Fin n → I) (z : ℂ) (order loop : ℕ) :
    expandInputs jetDelay w lower n F labels order loop * z =
      expandInputs jetDelay w lower n (fun xs r l => F xs r l * z) labels order loop := by
  have h := congrFun (congrFun (expand_smul jetDelay w lower n z F labels) order) loop
  have he : (fun xs => z • F xs) = (fun xs r l => F xs r l * z) := by
    funext xs r l
    exact mul_comm z (F xs r l)
  rw [he] at h
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

#print axioms expand_integrable
#print axioms expand_integral
#print axioms expand_tendsto
#print axioms expand_mul
end YMYMG.IncomingExpansion
