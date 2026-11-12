import CouplingTaylorShift

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Finite jet algebra used to transport the native invariant vacuum words.
No convergence, analyticity or interchange of infinite sums is involved. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.WordJet
open YMYMG.CouplingTaylor

abbrev Jet := ℕ → ℕ → ℂ

theorem convolve_comm (c w : Jet) (order loop : ℕ) :
    convolve c w order loop = convolve w c order loop := by
  unfold convolve
  apply Fintype.sum_equiv Fin.revPerm
  intro i
  apply Fintype.sum_equiv Fin.revPerm
  intro j
  have hi := i.add_rev_cast
  have hj := j.add_rev_cast
  have hi' : order - i.rev.val = i.val := by omega
  have hj' : loop - j.rev.val = j.val := by omega
  have hi'' : i.rev.val = order - i.val := by omega
  have hj'' : j.rev.val = loop - j.val := by omega
  simp only [Fin.revPerm_apply]
  rw [hi', hj', hi'', hj'', mul_comm]

theorem convolve_add_right (c w v : Jet) (order loop : ℕ) :
    convolve c (w + v) order loop =
      convolve c w order loop + convolve c v order loop := by
  simp only [convolve, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem convolve_smul_right (c w : Jet) (a : ℂ) (order loop : ℕ) :
    convolve c (a • w) order loop = a * convolve c w order loop := by
  simp only [convolve, Pi.smul_apply, smul_eq_mul, mul_left_comm,
    Finset.mul_sum]

theorem convolve_delay_right (c w : Jet) (order loop : ℕ) :
    convolve c (delay w) order loop = delay (convolve c w) order loop := by
  rw [convolve_comm, convolve_delay]
  exact congrArg (fun f : Jet => delay f order loop)
    (by funext i j; exact convolve_comm w c i j)

/-- The formal multiplication by one loop and two powers of the coupling. -/
def delayMap (X : Type*) : (X → Jet) →ₗ[ℂ] (X → Jet) where
  toFun F x := delay (F x)
  map_add' F H := by
    funext x order loop
    obtain order | order | order := order <;> cases loop <;> simp [delay]
  map_smul' a F := by
    funext x order loop
    obtain order | order | order := order <;> cases loop <;> simp [delay]

/-- One finite insertion, with its original output cutoff and position update. -/
def insertionMap {X M : Type*} (outputs : Finset M) (c : M → Jet)
    (put : X → M → X) : (X → Jet) →ₗ[ℂ] (X → Jet) where
  toFun F x order loop := ∑ m ∈ outputs, convolve (c m) (F (put x m)) order loop
  map_add' F H := by
    funext x order loop
    simp only [Pi.add_apply, convolve_add_right, Finset.sum_add_distrib]
  map_smul' a F := by
    funext x order loop
    simp only [Pi.smul_apply, convolve_smul_right, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply]

theorem insertionMap_delay {X M : Type*} (outputs : Finset M) (c : M → Jet)
    (put : X → M → X) (F : X → Jet) :
    insertionMap outputs c put (delayMap X F) =
      delayMap X (insertionMap outputs c put F) := by
  funext x order loop
  change (∑ m ∈ outputs, convolve (c m) (delay (F (put x m))) order loop) =
    delay (fun i j => ∑ m ∈ outputs, convolve (c m) (F (put x m)) i j) order loop
  simp only [convolve_delay_right]
  obtain order | order | order := order <;> cases loop <;> simp [delay]

#print axioms convolve_comm
#print axioms convolve_add_right
#print axioms convolve_smul_right
#print axioms convolve_delay_right
#print axioms delayMap
#print axioms insertionMap
#print axioms insertionMap_delay
end YMYMG.WordJet
