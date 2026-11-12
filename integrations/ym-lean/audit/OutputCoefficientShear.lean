import WordJetAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Finite outgoing coefficient transport at one fixed label cutoff.
The correction is contragredient to J'_i = J_i + a w_i delta J_k.
No infinite sums or physical independence assumptions are used. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.OutputRecovery
open YMYMG.CouplingTaylor YMYMG.WordJet

variable {n : ℕ}

def weighted (w : Fin n → ℝ) (c : ℕ → ℕ → Fin n → ℂ) : Jet :=
  fun order loop => ∑ i, (w i : ℂ) * c order loop i

def corrected (w : Fin n → ℝ) (k : Fin n) (a : ℝ)
    (c : ℕ → ℕ → Fin n → ℂ) : ℕ → ℕ → Fin n → ℂ :=
  fun order loop i => c order loop i -
    if i = k then (a : ℂ) * delay (weighted w c) order loop else 0

def assemble (c : ℕ → ℕ → Fin n → ℂ) (J : Fin n → Jet) : Jet :=
  fun order loop => ∑ i, convolve (fun r l => c r l i) (J i) order loop

theorem weighted_corrected (w : Fin n → ℝ) (k : Fin n) (a : ℝ)
    (c : ℕ → ℕ → Fin n → ℂ) (hk : w k = 0) :
    weighted w (corrected w k a c) = weighted w c := by
  classical
  funext order loop
  simp [weighted, corrected, mul_sub, mul_ite, hk, Finset.sum_sub_distrib]

theorem weighted_convolve (w : Fin n → ℝ) (c : ℕ → ℕ → Fin n → ℂ)
    (J : Jet) (order loop : ℕ) :
    convolve (weighted w c) J order loop =
      ∑ i, (w i : ℂ) * convolve (fun r l => c r l i) J order loop := by
  simp only [convolve, weighted, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem weighted_delay_convolve (w : Fin n → ℝ)
    (c : ℕ → ℕ → Fin n → ℂ) (J : Jet) (order loop : ℕ) :
    (∑ i, (w i : ℂ) * delay (convolve (fun r l => c r l i) J) order loop) =
      delay (convolve (weighted w c) J) order loop := by
  obtain order | order | order := order <;> cases loop
  all_goals simp only [delay, mul_zero, Finset.sum_const_zero]
  exact (weighted_convolve w c J _ _).symm

theorem assemble_dictionary_change (w : Fin n → ℝ) (a : ℝ)
    (c : ℕ → ℕ → Fin n → ℂ) (J : Fin n → Jet) (lower : Jet)
    (order loop : ℕ) :
    assemble c (fun i => J i + ((a : ℂ) * (w i : ℂ)) • delay lower) order loop =
      assemble c J order loop +
        (a : ℂ) * delay (convolve (weighted w c) lower) order loop := by
  simp only [assemble, convolve_add_right, convolve_smul_right,
    convolve_delay_right, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [weighted_delay_convolve]

theorem assemble_corrected (w : Fin n → ℝ) (k : Fin n) (a : ℝ)
    (c : ℕ → ℕ → Fin n → ℂ) (J : Fin n → Jet) (order loop : ℕ) :
    assemble (corrected w k a c) J order loop = assemble c J order loop -
      (a : ℂ) * delay (convolve (weighted w c) (J k)) order loop := by
  classical
  have hc (i : Fin n) :
      convolve (fun r l => corrected w k a c r l i) (J i) order loop =
        convolve (fun r l => c r l i) (J i) order loop -
          if i = k then (a : ℂ) * delay (convolve (weighted w c) (J k)) order loop
          else 0 := by
    by_cases hi : i = k
    · subst i
      simp only [corrected, ↓reduceIte, convolve, sub_mul, Finset.sum_sub_distrib]
      congr 1
      change convolve (fun r l => (a : ℂ) * delay (weighted w c) r l) (J k)
        order loop = _
      rw [convolve_const_mul, convolve_delay]
    · simp [corrected, hi]
  simp only [assemble, hc, Finset.sum_sub_distrib]
  simp

theorem assemble_cancel (w : Fin n → ℝ) (k : Fin n) (a : ℝ)
    (c : ℕ → ℕ → Fin n → ℂ) (J : Fin n → Jet) (hk : w k = 0)
    (order loop : ℕ) :
    assemble (corrected w k a c)
      (fun i => J i + ((a : ℂ) * (w i : ℂ)) • delay (J k)) order loop =
        assemble c J order loop := by
  rw [assemble_dictionary_change, weighted_corrected w k a c hk, assemble_corrected]
  ring

theorem corrected_graph_order (w : Fin n → ℝ) (k : Fin n) (a : ℝ)
    (c : ℕ → ℕ → Fin n → ℂ)
    (hc : ∀ order loop i, order < 2 * loop → c order loop i = 0)
    (order loop : ℕ) (i : Fin n) (h : order < 2 * loop) :
    corrected w k a c order loop i = 0 := by
  have hd : delay (weighted w c) order loop = 0 := by
    obtain order | order | order := order <;> cases loop
    all_goals simp only [delay]
    exact Finset.sum_eq_zero (fun j _ => by rw [hc _ _ j (by omega), mul_zero])
  simp [corrected, hc _ _ _ h, hd]

#print axioms weighted_corrected
#print axioms weighted_convolve
#print axioms weighted_delay_convolve
#print axioms assemble_dictionary_change
#print axioms assemble_corrected
#print axioms assemble_cancel
#print axioms corrected_graph_order
end YMYMG.OutputRecovery
