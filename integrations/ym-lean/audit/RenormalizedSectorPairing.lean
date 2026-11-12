import YangMills.FilteredQuantumRG

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
The complete three-channel Gaussian change of normal product, including
Q -> identity and Q² -> Q, inserted into the native stripping formula.
The Frame slice and the identification with physical generated data are
explicitly conditional. This is not an exhaustive actual-G basis instance.
-/
noncomputable section
open scoped BigOperators
namespace YMYMG.GaussianSector
open YangMills YangMills.PerturbativeFlow YangMills.FilteredRG

def heat3 (n s : ℂ) : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v i := if i = 0 then v 0 + n*s*v 1 + n*(n+2)*s^2*v 2
    else if i = 1 then v 1 + 2*(n+2)*s*v 2 else v 2
  invFun v i := if i = 0 then v 0 - n*s*v 1 + n*(n+2)*s^2*v 2
    else if i = 1 then v 1 - 2*(n+2)*s*v 2 else v 2
  left_inv v := by ext i; fin_cases i <;> simp; ring
  right_inv v := by ext i; fin_cases i <;> simp; ring
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

def heat2 (n s : ℂ) : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v i := if i = 0 then v 0 + n*s*v 1 else v 1
  invFun v i := if i = 0 then v 0 - n*s*v 1 else v 1
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp; ring
  map_smul' c v := by ext i; fin_cases i <;> simp; ring

theorem heat_overlap (n s : ℂ) (i j : Fin 2) :
    heat3 n s (Pi.single j.castSucc 1) i.castSucc = heat2 n s (Pi.single j 1) i := by
  fin_cases i <;> fin_cases j <;> simp [heat3, heat2]

theorem heat_composition (n s t : ℂ) (v : Fin 3 → ℂ) :
    heat3 n s (heat3 n t v) = heat3 n (s+t) v := by
  ext i
  fin_cases i <;> simp [heat3] <;> ring

/-- Only entries that can reach the Q output with these incoming columns
are supplied. The QQ -> identity entry cannot contribute to this output. -/
def channels (low unit : OPE.MultiDistribution 1) :
    (arity : ℕ) → (Fin arity → Fin 3) → Fin 3 → Fin 3 → OPE.MultiDistribution arity :=
  fun arity inputs last output => if h : arity = 1 then
    if inputs (Fin.cast h.symm 0) = 1 ∧ last = 1 then
      if output = 1 then h ▸ low else if output = 2 then h ▸ unit else 0
    else if ((inputs (Fin.cast h.symm 0) = 0 ∧ last = 1) ∨
        (inputs (Fin.cast h.symm 0) = 1 ∧ last = 0)) ∧ output = 1 then h ▸ unit else 0
  else 0

theorem sum_one_tuple {m : ℕ} (f : (Fin 1 → Fin m) → ℂ) :
    (∑ inputs, f inputs) = ∑ i, f (fun _ => i) := by
  classical
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin m)) _ _
    (fun inputs => congrArg f (funext (fun i => congrArg inputs (Subsingleton.elim i 0))))

variable {G : CompactSimpleGaugeGroup} {reference : RenormalizationScale}
  {beta : ℕ → ℝ}

theorem full_pairing {labels : Fin 3 → InvariantInsertionLabel G}
    {gamma : RenormalizationScale → ℕ → Fin 3 → Fin 3 → ℂ}
    (F : Frame labels reference beta gamma) (n d : ℂ)
    (low unit : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1)
    (hF : F.transport (YangMills.RG.time scale) = heat3 n (-d))
    (hdegree : OPE.dimension (labels 1) = 4) :
    strippedMultiPairing F (channels low unit) scale 1 (fun _ => 1) 1 1 test =
      (scale : ℂ)^4 * (low (OPE.dilateRelative scale test) -
        4*d*unit (OPE.dilateRelative scale test)) := by
  classical
  simp only [strippedMultiPairing, hF]
  rw [sum_one_tuple]
  norm_num [Fin.sum_univ_succ, channels, heat3, hdegree, Pi.single_apply, Fin.reduceFinMk]
  simp only [show (2 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    if_false, add_zero, zero_add, LinearMap.zero_apply]
  norm_cast
  ring

theorem small_pairing {labels : Fin 2 → InvariantInsertionLabel G}
    {gamma : RenormalizationScale → ℕ → Fin 2 → Fin 2 → ℂ}
    (F : Frame labels reference beta gamma) (n d : ℂ)
    (low unit : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1)
    (hF : F.transport (YangMills.RG.time scale) = heat2 n (-d))
    (hdegree : OPE.dimension (labels 1) = 4) :
    strippedMultiPairing F
      (fun arity inputs last output => channels low unit arity
        (fun i => (inputs i).castSucc) last.castSucc output.castSucc)
      scale 1 (fun _ => 1) 1 1 test =
      (scale : ℂ)^4 * (low (OPE.dilateRelative scale test) +
        2*n*d*unit (OPE.dilateRelative scale test)) := by
  classical
  simp only [strippedMultiPairing, hF]
  rw [sum_one_tuple]
  norm_num [Fin.sum_univ_succ, channels, heat2, hdegree, Pi.single_apply, Fin.reduceFinMk]
  norm_cast
  ring

/-- Comparison with all incoming identity terms retained. The unknown
lower-output distribution cancels; the missing high-output channel remains. -/
theorem sector_difference
    {labels3 : Fin 3 → InvariantInsertionLabel G}
    {labels2 : Fin 2 → InvariantInsertionLabel G}
    {gamma3 : RenormalizationScale → ℕ → Fin 3 → Fin 3 → ℂ}
    {gamma2 : RenormalizationScale → ℕ → Fin 2 → Fin 2 → ℂ}
    (large : Frame labels3 reference beta gamma3)
    (small : Frame labels2 reference beta gamma2) (n d : ℂ)
    (low unit : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1)
    (hl : large.transport (YangMills.RG.time scale) = heat3 n (-d))
    (hs : small.transport (YangMills.RG.time scale) = heat2 n (-d))
    (hdl : OPE.dimension (labels3 1) = 4)
    (hds : OPE.dimension (labels2 1) = 4) :
    strippedMultiPairing large (channels low unit) scale 1 (fun _ => 1) 1 1 test -
      strippedMultiPairing small
        (fun arity inputs last output => channels low unit arity
          (fun i => (inputs i).castSucc) last.castSucc output.castSucc)
        scale 1 (fun _ => 1) 1 1 test =
      -2*(n+2)*(scale : ℂ)^4*d*unit (OPE.dilateRelative scale test) := by
  rw [full_pairing large n d low unit scale test hl hdl,
    small_pairing small n d low unit scale test hs hds]
  ring

theorem difference_nonzero (n : ℕ) (d u : ℂ) (scale : ℝ)
    (hd : d ≠ 0) (hu : u ≠ 0) (hs : scale ≠ 0) :
    -2*((n : ℂ)+2)*(scale : ℂ)^4*d*u ≠ 0 := by
  have hn : (n : ℂ)+2 ≠ 0 := by
    exact_mod_cast (show (n : ℝ)+2 ≠ 0 by positivity)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) hn) (pow_ne_zero 4 (by exact_mod_cast hs))) hd) hu

/-- A complete finite Gaussian change removes the heat transport on this
three-label polynomial space, including the double-contraction unit term.
This is not a transformed full generated YM family. -/
theorem finite_gaussian_cancellation (n d : ℂ) (v : Fin 3 → ℂ) :
    heat3 n d (heat3 n (-d) v) = v := by
  rw [heat_composition]
  ext i
  fin_cases i <;> simp [heat3]

#print axioms heat3
#print axioms heat2
#print axioms heat_overlap
#print axioms heat_composition
#print axioms sum_one_tuple
#print axioms full_pairing
#print axioms small_pairing
#print axioms sector_difference
#print axioms difference_nonzero
#print axioms finite_gaussian_cancellation
end YMYMG.GaussianSector
