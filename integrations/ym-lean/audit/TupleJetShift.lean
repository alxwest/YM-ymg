import WordJetAlgebra
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Exact reindexing of the finite coupling/loop allocations in the native
Legendre partition sums. No coefficient series is summed to a function. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.TupleJet
open YMYMG.CouplingTaylor YMYMG.WordJet

theorem allocation_le {k n : ℕ} {v : Fin k → ℕ}
    (hv : v ∈ Finset.Nat.antidiagonalTuple k n) (i : Fin k) : v i ≤ n := by
  rw [← Finset.Nat.mem_antidiagonalTuple.mp hv]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (v j)) (Finset.mem_univ i)

theorem bounded_sum_eq_allocation (k n : ℕ) (f : (Fin k → ℕ) → ℂ) :
    (∑ v : Fin k → Fin (n+1),
      if (∑ i, (v i).val) = n then f (fun i => (v i).val) else 0) =
      ∑ v ∈ Finset.Nat.antidiagonalTuple k n, f v := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun v _ i => (v i).val)
  · intro v hv
    exact Finset.Nat.mem_antidiagonalTuple.mpr (Finset.mem_filter.mp hv).2
  · intro v hv w hw he
    funext i
    exact Fin.ext (congrFun he i)
  · intro v hv
    let w : Fin k → Fin (n+1) := fun i => ⟨v i, by have := allocation_le hv i; omega⟩
    refine ⟨w, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Nat.mem_antidiagonalTuple.mp hv⟩
  · intro v hv
    rfl

theorem bounded_pair_eq_allocation (k order loop : ℕ)
    (f : (Fin k → ℕ) → (Fin k → ℕ) → ℂ) :
    (∑ g : Fin k → Fin (order+1), ∑ h : Fin k → Fin (loop+1),
      if (∑ i, (g i).val) = order ∧ (∑ i, (h i).val) = loop then
        f (fun i => (g i).val) (fun i => (h i).val) else 0) =
    ∑ g ∈ Finset.Nat.antidiagonalTuple k order,
      ∑ h ∈ Finset.Nat.antidiagonalTuple k loop, f g h := by
  simp only [ite_and]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [bounded_sum_eq_allocation k order (fun g =>
    ∑ h : Fin k → Fin (loop+1),
      if (∑ i, (h i).val) = loop then f g (fun i => (h i).val) else 0)]
  apply Finset.sum_congr rfl
  intro g hg
  exact bounded_sum_eq_allocation k loop (f g)

def raiseHead {k : ℕ} (d : ℕ) (v : Fin (k+1) → ℕ) : Fin (k+1) → ℕ :=
  Fin.cons (v 0 + d) (fun i => v i.succ)

def lowerHead {k : ℕ} (d : ℕ) (v : Fin (k+1) → ℕ) : Fin (k+1) → ℕ :=
  Fin.cons (v 0 - d) (fun i => v i.succ)

theorem allocation_shift_head (k d n : ℕ) (f : (Fin (k+1) → ℕ) → ℂ) :
    (∑ v ∈ Finset.Nat.antidiagonalTuple (k+1) (n+d),
      if d ≤ v 0 then f (lowerHead d v) else 0) =
      ∑ v ∈ Finset.Nat.antidiagonalTuple (k+1) n, f v := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun v _ => raiseHead d v)
  · intro v hv
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.Nat.mem_antidiagonalTuple.mpr
      have hh := Finset.Nat.mem_antidiagonalTuple.mp hv
      rw [Fin.sum_univ_succ] at hh
      simp only [raiseHead, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega
    · simp [raiseHead]
  · intro v hv w hw he
    have h0 := congrFun he 0
    simp only [raiseHead, Fin.cons_zero] at h0
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · omega
    · exact congrFun he j.succ
  · intro v hv
    obtain ⟨hv, hd⟩ := Finset.mem_filter.mp hv
    have hh := Finset.Nat.mem_antidiagonalTuple.mp hv
    rw [Fin.sum_univ_succ] at hh
    refine ⟨lowerHead d v, ?_, ?_⟩
    · apply Finset.Nat.mem_antidiagonalTuple.mpr
      simp only [lowerHead, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega
    · funext i
      refine Fin.cases ?_ (fun j => rfl) i
      simp only [raiseHead, lowerHead, Fin.cons_zero]
      omega
  · intro v hv
    apply congrArg f
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    simp [raiseHead, lowerHead]

def tupleConvolve (k : ℕ) (c : Jet)
    (roots : (Fin k → ℕ) → (Fin k → ℕ) → ℂ) (order loop : ℕ) : ℂ :=
  ∑ g ∈ Finset.Nat.antidiagonalTuple (k+1) order,
    ∑ h ∈ Finset.Nat.antidiagonalTuple (k+1) loop,
      c (g 0) (h 0) * roots (fun i => g i.succ) (fun i => h i.succ)

theorem delay_if (c : Jet) (order loop : ℕ) :
    delay c order loop = if 2 ≤ order ∧ 1 ≤ loop then c (order-2) (loop-1) else 0 := by
  obtain order | order | order := order <;> cases loop <;> simp [delay]

theorem tupleConvolve_delay (k : ℕ) (c : Jet)
    (roots : (Fin k → ℕ) → (Fin k → ℕ) → ℂ) (order loop : ℕ) :
    tupleConvolve k (delay c) roots order loop =
      delay (tupleConvolve k c roots) order loop := by
  classical
  by_cases hr : 2 ≤ order
  · by_cases hl : 1 ≤ loop
    · obtain ⟨r, rfl⟩ : ∃ r, order = r+2 := ⟨order-2, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, loop = l+1 := ⟨loop-1, by omega⟩
      simp only [tupleConvolve, delay_if, ite_and, ite_mul, zero_mul,
        Finset.sum_ite_irrel, Finset.sum_const_zero]
      change (∑ g ∈ Finset.Nat.antidiagonalTuple (k+1) (r+2),
        if 2 ≤ g 0 then
          (fun v => ∑ h ∈ Finset.Nat.antidiagonalTuple (k+1) (l+1),
            if 1 ≤ h 0 then c (v 0) (h 0-1) *
              roots (fun i => v i.succ) (fun i => h i.succ) else 0) (lowerHead 2 g)
        else 0) = _
      rw [allocation_shift_head k 2 r (fun v =>
        ∑ h ∈ Finset.Nat.antidiagonalTuple (k+1) (l+1),
          if 1 ≤ h 0 then c (v 0) (h 0-1) *
            roots (fun i => v i.succ) (fun i => h i.succ) else 0)]
      simp only [show 2 ≤ r+2 by omega, show 1 ≤ l+1 by omega, if_true,
        Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro g hg
      exact allocation_shift_head k 1 l
        (fun h => c (g 0) (h 0) * roots (fun i => g i.succ) (fun i => h i.succ))
    · rw [delay_if, if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro g hg
      apply Finset.sum_eq_zero
      intro h hh
      have hb := allocation_le hh 0
      simp [delay_if, show ¬ (2 ≤ g 0 ∧ 1 ≤ h 0) by omega]
  · rw [delay_if, if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro g hg
    apply Finset.sum_eq_zero
    intro h hh
    have hb := allocation_le hg 0
    simp [delay_if, show ¬ (2 ≤ g 0 ∧ 1 ≤ h 0) by omega]

#print axioms allocation_le
#print axioms bounded_sum_eq_allocation
#print axioms bounded_pair_eq_allocation
#print axioms allocation_shift_head
#print axioms delay_if
#print axioms tupleConvolve_delay
end YMYMG.TupleJet
