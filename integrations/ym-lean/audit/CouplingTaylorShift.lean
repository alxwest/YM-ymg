import YangMills.QuantumObservableLift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.CouplingTaylor

def jet (order : ℕ) (f : ℝ → ℂ) : ℂ :=
  (order.factorial : ℂ)⁻¹ * iteratedDeriv order f 0

theorem jet_add (order : ℕ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    jet order (fun x => f x + g x) = jet order f + jet order g := by
  unfold jet
  rw [iteratedDeriv_fun_add
    (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)))]
  ring

theorem jet_const_mul (order : ℕ) (a : ℂ) (f : ℝ → ℂ) :
    jet order (fun x => a * f x) = a * jet order f := by
  simp only [jet, iteratedDeriv_const_mul_field]
  ring

theorem jet_mul_square (order : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    jet order (fun x => (x : ℂ)^2 * f x) =
      if 2 ≤ order then jet (order-2) f else 0 := by
  have hd := iteratedDerivWithin_smul (𝕜 := ℝ) (𝔸 := ℝ) (F := ℂ)
    (n := order) (x := 0) (s := Set.univ)
    (f := fun x : ℝ => x^2) (g := f) (Set.mem_univ 0) uniqueDiffOn_univ
    (by fun_prop)
    (hf.contDiffAt.contDiffWithinAt.of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)))
  simp only [iteratedDerivWithin_univ, iteratedDeriv_fun_pow_zero] at hd
  change iteratedDeriv order (fun x : ℝ => x^2 • f x) 0 = _ at hd
  have he : (fun x : ℝ => (x : ℂ)^2 * f x) = fun x : ℝ => x^2 • f x := by
    funext x
    simp [Complex.real_smul]
  unfold jet
  rw [he, hd]
  by_cases hn : 2 ≤ order
  · rw [if_pos hn, Finset.sum_eq_single 2]
    · norm_num
      have hfac : (order.choose 2 : ℂ) * 2 * ((order-2).factorial : ℂ) =
          (order.factorial : ℂ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hn
      have h0 : (order.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero order
      have h1 : ((order-2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (order-2)
      field_simp
      linear_combination iteratedDeriv (order-2) f 0 * hfac
    · intro i _ hi
      simp [hi]
    · intro hi
      exact False.elim (hi (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hn]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i hi
    have hi2 : i ≠ 2 := by have := Finset.mem_range.mp hi; omega
    simp [hi2]

def delay {E : Type*} [Zero E] (c : ℕ → ℕ → E) : ℕ → ℕ → E
  | order+2, loop+1 => c order loop
  | _, _ => 0

theorem map_delay {E F : Type*} [Zero E] [Zero F] (T : E → F) (hT : T 0 = 0)
    (c : ℕ → ℕ → E) (order loop : ℕ) :
    T (delay c order loop) = delay (fun i j => T (c i j)) order loop := by
  obtain order | order | order := order <;> cases loop <;> simp [delay, hT]

theorem delay_tendsto {X : Type*} {F : Filter X}
    (f : X → ℕ → ℕ → ℂ) (g : ℕ → ℕ → ℂ)
    (h : ∀ order loop, Filter.Tendsto (fun x => f x order loop) F (nhds (g order loop)))
    (order loop : ℕ) :
    Filter.Tendsto (fun x => delay (f x) order loop) F (nhds (delay g order loop)) := by
  obtain order | order | order := order <;> cases loop
  all_goals first | exact h _ _ | exact tendsto_const_nhds

def convolve (c w : ℕ → ℕ → ℂ) (order loop : ℕ) : ℂ :=
  ∑ i : Fin (order+1), ∑ j : Fin (loop+1), c i.val j.val * w (order-i.val) (loop-j.val)

theorem convolve_add (c d w : ℕ → ℕ → ℂ) (order loop : ℕ) :
    convolve (fun i j => c i j + d i j) w order loop =
      convolve c w order loop + convolve d w order loop := by
  simp only [convolve, add_mul, Finset.sum_add_distrib]

theorem convolve_const_mul (a : ℂ) (c w : ℕ → ℕ → ℂ) (order loop : ℕ) :
    convolve (fun i j => a*c i j) w order loop = a*convolve c w order loop := by
  simp only [convolve, mul_assoc, Finset.mul_sum]

theorem convolve_delay (c w : ℕ → ℕ → ℂ) (order loop : ℕ) :
    convolve (delay c) w order loop = delay (convolve c w) order loop := by
  cases loop with
  | zero => simp [convolve, delay]
  | succ loop =>
    cases order with
    | zero => simp [convolve, delay]
    | succ order =>
      cases order with
      | zero => simp [convolve, delay, Fin.sum_univ_succ]
      | succ order =>
        change convolve (delay c) w (order+2) (loop+1) = convolve c w order loop
        unfold convolve
        conv_lhs => rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, delay, zero_mul, Finset.sum_const_zero, zero_add,
          Fin.val_succ]
        conv_lhs => rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, zero_mul, Finset.sum_const_zero, zero_add,
          Fin.val_succ, Nat.add_sub_add_right]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, zero_mul, zero_add, Fin.val_succ,
          Nat.add_sub_add_right]

#print axioms jet_add
#print axioms jet_const_mul
#print axioms jet_mul_square
#print axioms convolve_add
#print axioms convolve_const_mul
#print axioms convolve_delay
#print axioms map_delay
#print axioms delay_tendsto
end YMYMG.CouplingTaylor
