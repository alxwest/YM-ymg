import IncomingExpansionAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Smooth coupling derivatives of the finite incoming change. The actual
factor g^2 and the consumed loop order give precisely the (2,1) jet shift. -/
noncomputable section
open scoped ContDiff
namespace YMYMG.IncomingExpansion
open YMYMG.CouplingTaylor

def finiteTransform {I : Type*} (w : I → ℝ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → ℝ → ℕ → ℂ) (labels : Fin n → I) (g : ℝ) : ℕ → ℂ :=
  expandInputs loopDelay (fun p => (g : ℂ)^2 * (w p : ℂ)) lower n (fun xs => F xs g) labels

theorem finiteTransform_zero {I : Type*} (w : I → ℝ) (lower : I) (n : ℕ)
    (F : (Fin (n+1) → I) → ℝ → ℕ → ℂ) (labels : Fin (n+1) → I) (g : ℝ) :
    finiteTransform w lower (n+1) F labels g 0 =
      finiteTransform w lower n (fun xs => F (Fin.cons (labels 0) xs)) (Fin.tail labels) g 0 := by
  simp [finiteTransform, expandInputs, loopDelay_zero]

theorem finiteTransform_succ {I : Type*} (w : I → ℝ) (lower : I) (n : ℕ)
    (F : (Fin (n+1) → I) → ℝ → ℕ → ℂ) (labels : Fin (n+1) → I) (g : ℝ) (loop : ℕ) :
    finiteTransform w lower (n+1) F labels g (loop+1) =
      finiteTransform w lower n (fun xs => F (Fin.cons (labels 0) xs)) (Fin.tail labels) g (loop+1) +
      ((g : ℂ)^2 * (w (labels 0) : ℂ)) *
        finiteTransform w lower n (fun xs => F (Fin.cons lower xs)) (Fin.tail labels) g loop := by
  simp only [finiteTransform, expandInputs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, loopDelay_succ]

theorem finiteTransform_smooth {I : Type*} (w : I → ℝ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → ℝ → ℕ → ℂ)
    (hF : ∀ xs loop, ContDiff ℝ ∞ (fun g => F xs g loop))
    (labels : Fin n → I) (loop : ℕ) :
    ContDiff ℝ ∞ (fun g => finiteTransform w lower n F labels g loop) := by
  induction n generalizing loop with
  | zero => exact hF labels loop
  | succ n ih =>
    cases loop with
    | zero =>
      simp only [finiteTransform_zero]
      exact ih _ (fun xs l => hF (Fin.cons (labels 0) xs) l) _ _
    | succ loop =>
      simp only [finiteTransform_succ]
      exact (ih _ (fun xs l => hF (Fin.cons (labels 0) xs) l) _ _).add
        (((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul
          (ih _ (fun xs l => hF (Fin.cons lower xs) l) _ _))

theorem finiteTransform_graph {I : Type*} (w : I → ℝ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → ℝ → ℕ → ℂ) (external : ℕ)
    (hF : ∀ xs g loop, F xs g loop = (g : ℂ)^(external+2*loop) * F xs 1 loop)
    (labels : Fin n → I) (g : ℝ) (loop : ℕ) :
    finiteTransform w lower n F labels g loop =
      (g : ℂ)^(external+2*loop) * finiteTransform w lower n F labels 1 loop := by
  induction n generalizing g loop with
  | zero => exact hF labels g loop
  | succ n ih =>
    cases loop with
    | zero =>
      simp only [finiteTransform_zero]
      exact ih _ (fun xs g l => hF (Fin.cons (labels 0) xs) g l) _ _ _
    | succ loop =>
      simp only [finiteTransform_succ]
      rw [ih _ (fun xs g l => hF (Fin.cons (labels 0) xs) g l),
        ih _ (fun xs g l => hF (Fin.cons lower xs) g l)]
      simp only [Complex.ofReal_one, one_pow, one_mul]
      rw [show external+2*(loop+1) = (external+2*loop)+2 by omega, pow_add]
      ring

theorem finiteTransform_jet {I : Type*} (w : I → ℝ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → ℝ → ℕ → ℂ)
    (hF : ∀ xs loop, ContDiff ℝ ∞ (fun g => F xs g loop))
    (labels : Fin n → I) (order loop : ℕ) :
    jet order (fun g => finiteTransform w lower n F labels g loop) =
      expandInputs jetDelay (fun p => (w p : ℂ)) lower n
        (fun xs r l => jet r (fun g => F xs g l)) labels order loop := by
  induction n generalizing order loop with
  | zero => rfl
  | succ n ih =>
    have hp (l : ℕ) := finiteTransform_smooth w lower n
      (fun xs => F (Fin.cons (labels 0) xs)) (fun xs l => hF (Fin.cons (labels 0) xs) l)
      (Fin.tail labels) l
    have hq (l : ℕ) := finiteTransform_smooth w lower n
      (fun xs => F (Fin.cons lower xs)) (fun xs l => hF (Fin.cons lower xs) l)
      (Fin.tail labels) l
    cases loop with
    | zero =>
      simp only [finiteTransform_zero, expandInputs, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, jetDelay_apply]
      have hd : ∀ J : ℕ → ℕ → ℂ, delay J order 0 = 0 := by
        intro J; obtain order | order | order := order <;> rfl
      simp only [hd, mul_zero, add_zero]
      exact ih _ (fun xs l => hF (Fin.cons (labels 0) xs) l) _ _ _
    | succ loop =>
      simp only [finiteTransform_succ]
      have hs : ContDiff ℝ ∞ (fun g : ℝ => ((g : ℂ)^2 * (w (labels 0) : ℂ)) *
          finiteTransform w lower n (fun xs => F (Fin.cons lower xs)) (Fin.tail labels) g loop) :=
        (((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul (hq loop))
      rw [jet_add _ _ _ (hp (loop+1)) hs]
      have he : (fun g : ℝ => ((g : ℂ)^2 * (w (labels 0) : ℂ)) *
          finiteTransform w lower n (fun xs => F (Fin.cons lower xs)) (Fin.tail labels) g loop) =
          fun g : ℝ => (w (labels 0) : ℂ) * ((g : ℂ)^2 *
            finiteTransform w lower n (fun xs => F (Fin.cons lower xs)) (Fin.tail labels) g loop) := by
        funext g; ring
      rw [he, jet_const_mul, jet_mul_square _ _ (hq loop)]
      rw [ih _ (fun xs l => hF (Fin.cons (labels 0) xs) l)]
      simp only [expandInputs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jetDelay_apply]
      obtain order | order | order := order
      · simp [delay]
      · simp [delay]
      · simp only [show 2 ≤ order+1+1 by omega, ↓reduceIte,
          show order+1+1-2 = order by omega, delay]
        rw [ih _ (fun xs l => hF (Fin.cons lower xs) l)]

#print axioms finiteTransform_zero
#print axioms finiteTransform_succ
#print axioms finiteTransform_smooth
#print axioms finiteTransform_graph
#print axioms finiteTransform_jet
end YMYMG.IncomingExpansion
