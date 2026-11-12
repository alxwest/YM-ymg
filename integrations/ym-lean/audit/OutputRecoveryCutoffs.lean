import OutputCoefficientShear

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Exact cutoff-coherence tests for the outgoing coefficient correction.
The finite model below has two independent physical directions and no
exact remainder. It is not a Yang--Mills model or an existence counterexample. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.OutputRecoveryCutoffs
open YMYMG.CouplingTaylor YMYMG.WordJet YMYMG.OutputRecovery

def weightedOn {I : Type*} (active : Finset I) (w : I → ℝ)
    (c : ℕ → ℕ → I → ℂ) : Jet :=
  fun order loop => ∑ i ∈ active, (w i : ℂ) * c order loop i

def correctedOn {I : Type*} [DecidableEq I] (active : Finset I) (w : I → ℝ)
    (lower : I) (a : ℝ) (c : ℕ → ℕ → I → ℂ) : ℕ → ℕ → I → ℂ :=
  fun order loop i => c order loop i -
    if i = lower then (a : ℂ) * delay (weightedOn active w c) order loop else 0

/-- The finite-index correction used by native recovery is the restriction
of the active-set correction, independently of the enumeration order. -/
theorem weighted_enumeration {I : Type*} [DecidableEq I] {n : ℕ}
    (index : Fin n → I) (hinj : Function.Injective index)
    (w : I → ℝ) (c : ℕ → ℕ → I → ℂ) :
    weightedOn (Finset.univ.image index) w c =
      weighted (fun i => w (index i)) (fun r l i => c r l (index i)) := by
  funext order loop
  exact Finset.sum_image (fun _ _ _ _ h => hinj h)

theorem corrected_enumeration {I : Type*} [DecidableEq I] {n : ℕ}
    (index : Fin n → I) (hinj : Function.Injective index)
    (w : I → ℝ) (k : Fin n) (a : ℝ) (c : ℕ → ℕ → I → ℂ)
    (order loop : ℕ) (i : Fin n) :
    corrected (fun j => w (index j)) k a (fun r l j => c r l (index j)) order loop i =
      correctedOn (Finset.univ.image index) w (index k) a c order loop (index i) := by
  simp only [corrected, correctedOn, weighted_enumeration index hinj, hinj.eq_iff]

/-- The discrepancy is precisely the omitted weighted high-output tail. -/
theorem correction_cutoff_difference {I : Type*} [DecidableEq I]
    (small large : Finset I) (hsub : small ⊆ large) (w : I → ℝ)
    (lower : I) (a : ℝ) (c : ℕ → ℕ → I → ℂ) (order loop : ℕ) :
    correctedOn large w lower a c (order+2) (loop+1) lower -
        correctedOn small w lower a c (order+2) (loop+1) lower =
      -(a : ℂ) * weightedOn (large \ small) w c order loop := by
  have hs : weightedOn (large \ small) w c order loop =
      weightedOn large w c order loop - weightedOn small w c order loop :=
    eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  simp only [correctedOn, ↓reduceIte, delay]
  rw [hs]
  ring

/-- Equality of these corrected coefficients on overlapping active sets
holds exactly when every coefficient of the omitted weighted tail vanishes
after multiplication by the correction amplitude. -/
theorem correction_coherent_iff {I : Type*} [DecidableEq I]
    (small large : Finset I) (hsub : small ⊆ large) (w : I → ℝ)
    (lower : I) (hlower : lower ∈ small) (a : ℝ) (c : ℕ → ℕ → I → ℂ) :
    (∀ order loop i, i ∈ small →
      correctedOn large w lower a c order loop i =
        correctedOn small w lower a c order loop i) ↔
      ∀ order loop, (a : ℂ) * weightedOn (large \ small) w c order loop = 0 := by
  constructor
  · intro he order loop
    have hd := correction_cutoff_difference small large hsub w lower a c order loop
    rw [he _ _ lower hlower, sub_self] at hd
    linear_combination hd
  · intro htail order loop i _
    by_cases hi : i = lower
    · subst i
      obtain order | order | order := order <;> cases loop
      all_goals try { solve | simp [correctedOn, delay] }
      apply sub_eq_zero.mp
      rw [correction_cutoff_difference small large hsub]
      rw [neg_mul, htail, neg_zero]
    · simp [correctedOn, hi]

def unitJet : Jet := fun order loop => if order = 0 ∧ loop = 0 then 1 else 0

theorem unitJet_convolve (J : Jet) (order loop : ℕ) :
    convolve unitJet J order loop = J order loop := by
  unfold convolve
  rw [Finset.sum_eq_single (0 : Fin (order+1))]
  · rw [Finset.sum_eq_single (0 : Fin (loop+1))]
    · simp [unitJet]
    · intro j _ hj
      have hj0 : j.val ≠ 0 := fun he => hj (Fin.ext he)
      simp [unitJet, hj0]
    · simp
  · intro i _ hi
    have hi0 : i.val ≠ 0 := fun he => hi (Fin.ext he)
    simp [unitJet, hi0]
  · simp

theorem convolve_unitJet (J : Jet) (order loop : ℕ) :
    convolve J unitJet order loop = J order loop := by
  rw [convolve_comm, unitJet_convolve]

/-- Coordinate evaluations of L' = L and H' = H + a delta L. -/
def twoLabelFields (a : ℝ) (label coordinate : Fin 2) : Jet :=
  if label = 0 then (if coordinate = 0 then unitJet else 0)
  else if coordinate = 0 then (a : ℂ) • delay unitJet else unitJet

theorem twoLabel_assemble_low (a : ℝ) (c : ℕ → ℕ → Fin 2 → ℂ)
    (order loop : ℕ) :
    assemble c (fun i => twoLabelFields a i 0) order loop =
      c order loop 0 + (a : ℂ) * delay (fun r l => c r l 1) order loop := by
  simp only [assemble, Fin.sum_univ_two]
  change convolve (fun r l => c r l 0) unitJet order loop +
    convolve (fun r l => c r l 1) ((a : ℂ) • delay unitJet) order loop = _
  rw [convolve_unitJet, convolve_smul_right, convolve_delay_right]
  rw [show convolve (fun r l => c r l 1) unitJet = (fun r l => c r l 1) from
    funext (fun r => funext (fun l => convolve_unitJet _ r l))]

theorem twoLabel_assemble_high (a : ℝ) (c : ℕ → ℕ → Fin 2 → ℂ)
    (order loop : ℕ) :
    assemble c (fun i => twoLabelFields a i 1) order loop = c order loop 1 := by
  have hz (J : Jet) : convolve J 0 order loop = 0 := by simp [convolve]
  simp [assemble, Fin.sum_univ_succ, twoLabelFields, convolve_unitJet, hz]

/-- Recovery in the small sector sees only L. The large sector uses both
coordinates of exactly the preceding finite Cauchy-convolution assembly. -/
def SimultaneousRecovery (a : ℝ) (rawLow rawHigh low high : Jet) : Prop :=
  low = rawLow ∧ low + (a : ℂ) • delay high = rawLow ∧ high = rawHigh

/-- A shared coefficient pair exists exactly when the high tail is killed.
No claim that actual generated Yang--Mills coefficients meet or violate this
condition is made. -/
theorem simultaneous_iff (a : ℝ) (rawLow rawHigh : Jet) :
    (∃ low high, SimultaneousRecovery a rawLow rawHigh low high) ↔
      ∀ order loop, (a : ℂ) * rawHigh order loop = 0 := by
  constructor
  · rintro ⟨low, high, hlow, hfull, hhigh⟩ order loop
    rw [hlow, hhigh] at hfull
    have he := congrFun (congrFun hfull (order+2)) (loop+1)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, delay, add_eq_left] using he
  · intro hz
    refine ⟨rawLow, rawHigh, rfl, ?_, rfl⟩
    funext order loop
    obtain order | order | order := order <;> cases loop
    all_goals simp [delay, hz]

/-- Full-space inversion always works; the obstruction is simultaneous
agreement with the smaller raw projection, not invertibility of the shear. -/
theorem full_recovery (a : ℝ) (rawLow rawHigh : Jet) :
    (rawLow - (a : ℂ) • delay rawHigh) + (a : ℂ) • delay rawHigh = rawLow := by
  exact sub_add_cancel _ _

theorem unchanged_recovery (rawLow rawHigh : Jet) :
    SimultaneousRecovery 0 rawLow rawHigh rawLow rawHigh := by
  simp [SimultaneousRecovery]

/-- Nonzero leading high coefficient forces a discrepancy already at (2,1). -/
theorem leading_tail_obstruction (a : ℝ) (rawLow rawHigh : Jet)
    (ha : a ≠ 0) (hh : rawHigh 0 0 ≠ 0) :
    ¬ ∃ low high, SimultaneousRecovery a rawLow rawHigh low high := by
  rw [simultaneous_iff]
  intro h
  exact mul_ne_zero (by exact_mod_cast ha) hh (h 0 0)

theorem unit_tail_obstruction :
    ¬ ∃ low high, SimultaneousRecovery 1 0 unitJet low high := by
  exact leading_tail_obstruction 1 0 unitJet (by norm_num) (by simp [unitJet])

/-- The diagnostic respects the graph-order lower bound on coefficients. -/
theorem unitJet_graph (order loop : ℕ) (h : order < 2 * loop) :
    unitJet order loop = 0 := by
  have hn : ¬ (order = 0 ∧ loop = 0) := by omega
  simp [unitJet, hn]

#print axioms weighted_enumeration
#print axioms corrected_enumeration
#print axioms correction_cutoff_difference
#print axioms correction_coherent_iff
#print axioms unitJet_convolve
#print axioms convolve_unitJet
#print axioms twoLabel_assemble_low
#print axioms twoLabel_assemble_high
#print axioms simultaneous_iff
#print axioms full_recovery
#print axioms unchanged_recovery
#print axioms leading_tail_obstruction
#print axioms unit_tail_obstruction
#print axioms unitJet_graph
end YMYMG.OutputRecoveryCutoffs
