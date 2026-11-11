import YangMills.FilteredQuantumRG
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open YangMills YangMills.PerturbativeFlow YangMills.FilteredRG

namespace YMYMGAudit

/-- A pure outgoing high-label channel. For the probe only the pair with both
incoming labels 1 is observed. This is test data, not a physical candidate. -/
def highChannel (L : OPE.MultiDistribution 1) :
    (n : ℕ) → (Fin n → Fin 3) → Fin 3 → Fin 3 → OPE.MultiDistribution n :=
  fun n inputs last k => if h : n = 1 then
    if inputs (Fin.cast h.symm 0) = 1 ∧ last = 1 ∧ k = 2 then h ▸ L else 0
  else 0

variable {G : CompactSimpleGaugeGroup}
  {labels : Fin 3 → InvariantInsertionLabel G}
  {reference : RenormalizationScale} {beta : ℕ → ℝ}
  {gamma : RenormalizationScale → ℕ → Fin 3 → Fin 3 → ℂ}

/-- Exact evaluation of the ACTIVE stripping definition. The incoming
column is fixed, but the outgoing high label can feed a lower-degree slot. -/
theorem highChannel_stripped (F : Frame labels reference beta gamma)
    (L : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1)
    (output : Fin 3)
    (incoming : (F.transport (RG.time scale)).symm (Pi.single 1 1) 1 = 1) :
    strippedMultiPairing F (highChannel L) scale 1 (fun _ => 1) 1 output test =
      (((scale ^ ((2 : ℤ) * OPE.dimension (labels 1) - OPE.dimension (labels output)) : ℝ)) : ℂ) *
      F.transport (RG.time scale) (Pi.single 2 1) output *
      L (OPE.dilateRelative scale test) := by
  classical
  simp [strippedMultiPairing, highChannel, Fin.sum_univ_succ, two_mul]
  simp only [incoming, mul_one]
  rw [Finset.sum_eq_single (fun _ : Fin 1 => (1 : Fin 3))]
  · simp [incoming]
  · intro x _ hx
    have hn : x 0 ≠ 1 := by
      intro he
      apply hx
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using he
    simp [hn]
  · simp

/-- The literal restriction to the first two labels loses the whole channel. -/
theorem highChannel_restrict (L : OPE.MultiDistribution 1) (n : ℕ)
    (inputs : Fin n → Fin 2) (last output : Fin 2) :
    highChannel L n (fun r => (inputs r).castSucc) last.castSucc output.castSucc = 0 := by
  classical
  have hne : output.castSucc ≠ (2 : Fin 3) := by
    fin_cases output <;> decide
  simp [highChannel, hne]

/-- This evaluates the ACTIVE formula in the smaller sector, not a rewritten
stand-in. Its frame may be any admissible two-label frame. -/
theorem restricted_stripped_zero
    {smallLabels : Fin 2 → InvariantInsertionLabel G}
    {smallGamma : RenormalizationScale → ℕ → Fin 2 → Fin 2 → ℂ}
    (F : Frame smallLabels reference beta smallGamma)
    (L : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1)
    (output : Fin 2) :
    strippedMultiPairing F
      (fun n inputs last out => highChannel L n (fun r => (inputs r).castSucc)
        last.castSucc out.castSucc) scale 1 (fun _ => 1) 1 output test = 0 := by
  simp [strippedMultiPairing, highChannel_restrict]

/-- Explicit invertible filtered transport: the degree-eight label may mix
into the degree-four label, while the degree-four incoming column is fixed. -/
def shear (a : ℂ) : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := fun i => if i = 1 then v 1 + a * v 2 else v i
  invFun v := fun i => if i = 1 then v 1 - a * v 2 else v i
  left_inv v := by funext i; by_cases hi : i = 1 <;> simp [hi]
  right_inv v := by funext i; by_cases hi : i = 1 <;> simp [hi]
  map_add' v w := by funext i; by_cases hi : i = 1 <;> simp [hi]; ring
  map_smul' c v := by funext i; by_cases hi : i = 1 <;> simp [hi]; ring

theorem shear_incoming (a : ℂ) : (shear a).symm (Pi.single 1 1) = Pi.single 1 1 := by
  ext i
  simp [shear, Pi.single_apply]

theorem shear_outgoing (a : ℂ) : shear a (Pi.single 2 1) 1 = a := by
  simp [shear]

/-- Enlarging identity transport by the shear keeps every old matrix entry.
Thus agreement of overlapping frame entries alone does not remove the tail. -/
theorem shear_overlap (a : ℂ) (i j : Fin 2) :
    shear a (Pi.single j.castSucc 1) i.castSucc = (Pi.single j (1 : ℂ) : Fin 2 → ℂ) i := by
  fin_cases i <;> fin_cases j <;> simp [shear]

/-- An unconditional finite-dimensional counterexample to commuting a
low-output projection through coherent downward-filtered transport. -/
theorem projection_shear_failure :
    (fun i : Fin 2 => shear (1 : ℂ) (Pi.single 2 1) i.castSucc) ≠
      (fun i : Fin 2 => (Pi.single 2 (1 : ℂ) : Fin 3 → ℂ) i.castSucc) := by
  intro he
  have hv := congrFun he 1
  norm_num [shear, Pi.single_apply] at hv

/-- With degrees (0,4,8), the shear obeys precisely the frame's one-sided
filtration condition. It is not an impermissible upward mixing. -/
theorem shear_filtered (a : ℂ) (i j : Fin 3)
    (above : 4*j.val < 4*i.val) :
    shear a (Pi.single j 1) i = 0 := by
  have hji : j ≠ i := by
    intro he
    subst j
    omega
  by_cases hi : i = 1
  · subst i
    have hj2 : j ≠ 2 := by
      intro he
      subst j
      norm_num at above
    simp [shear, hji, hj2]
  · simp [shear, hi, hji]

/-- Actual stripping exposes the tail for a transport whose slice is this
explicit shear. No full physical candidate or generated-flow witness is asserted. -/
theorem shear_stripped (F : Frame labels reference beta gamma)
    (L : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1) (a : ℂ)
    (hF : F.transport (RG.time scale) = shear a)
    (degree : OPE.dimension (labels 1) = 4)
    (observation : L (OPE.dilateRelative scale test) = 1) :
    strippedMultiPairing F (highChannel L) scale 1 (fun _ => 1) 1 1 test =
      (scale : ℂ)^4 * a := by
  rw [highChannel_stripped F L scale test 1]
  · norm_num [degree, hF, shear_outgoing, observation]
    left
    norm_cast
  · rw [hF, shear_incoming]
    simp

/-- Small versus large ACTIVE stripping, at one fixed scale. This is a
conditional probe of the formula, not a full generated-sector countermodel. -/
theorem finite_sector_discrepancy
    {smallLabels : Fin 2 → InvariantInsertionLabel G}
    {smallGamma : RenormalizationScale → ℕ → Fin 2 → Fin 2 → ℂ}
    (small : Frame smallLabels reference beta smallGamma)
    (large : Frame labels reference beta gamma)
    (L : OPE.MultiDistribution 1) (scale : ℝ) (test : OPE.RelativeTest 1) (a : ℂ)
    (hF : large.transport (RG.time scale) = shear a)
    (degree : OPE.dimension (labels 1) = 4)
    (observation : L (OPE.dilateRelative scale test) = 1)
    (hs : scale ≠ 0) (ha : a ≠ 0) :
    strippedMultiPairing small
      (fun n inputs last out => highChannel L n (fun r => (inputs r).castSucc)
        last.castSucc out.castSucc) scale 1 (fun _ => 1) 1 1 test ≠
      strippedMultiPairing large (highChannel L) scale 1 (fun _ => 1) 1 1 test := by
  rw [restricted_stripped_zero, shear_stripped large L scale test a hF degree observation]
  exact Ne.symm (mul_ne_zero (pow_ne_zero 4 (by exact_mod_cast hs)) ha)

/-- A scalar diagnostic profile, not a supplied Yang--Mills coefficient.
For g(t)=(1+2t)^(-1/2), this is g(t)^2 on t>=0. -/
def gSquared (t : ℝ) : ℝ := (1 + 2*t)⁻¹

def shearProfile (t : ℝ) : ℝ := Real.exp (4*t) * gSquared t - 1

def tail (t : ℝ) : ℝ := gSquared t - Real.exp (-4*t)

def tailRatio (t : ℝ) : ℝ := 1 - (1+2*t)*Real.exp (-4*t)

theorem shearProfile_initial : shearProfile 0 = 0 := by
  norm_num [shearProfile, gSquared]

theorem rgTime_exp_neg (t : ℝ) : RG.time (Real.exp (-t)) = t := by
  simp [RG.time, Real.exp_neg]

/-- The transport profile has a smooth polynomial-in-g generator:
exp(4t) * (4g^2 - 2g^4), for g^2=(1+2t)^-1. -/
theorem shearProfile_derivative (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt shearProfile
      (Real.exp (4*t) * (4*gSquared t - 2*(gSquared t)^2)) t := by
  have hn : 1 + 2*t ≠ 0 := by linarith
  have hlin : HasDerivAt (fun s : ℝ => 1+2*s) 2 t := by
    simpa only [mul_one] using! ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add 1
  have hinv := hlin.inv hn
  have hexp := (Real.hasDerivAt_exp (4*t)).comp t ((hasDerivAt_id t).const_mul 4)
  have hd := (hexp.mul hinv).sub_const 1
  have he : Real.exp (4*t) * (4*1) * (1+2*t)⁻¹ +
      Real.exp (4*t) * (-2 / (1+2*t)^2) =
        Real.exp (4*t) * (4*gSquared t - 2*(gSquared t)^2) := by
    dsimp [gSquared]
    field_simp
    ring
  simpa only [shearProfile, Function.comp_def, Pi.mul_apply, Pi.inv_apply, he]
    using! hd

/-- A degree-four downward mixing term can survive the canonical lambda^4
factor. It is not enough to assert that high-degree outputs are suppressed. -/
theorem scaled_shearProfile (t : ℝ) :
    Real.exp (-t)^4 * shearProfile t = tail t := by
  have hp : Real.exp (-t)^4 = Real.exp (-4*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc : Real.exp (-4*t) * Real.exp (4*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  simp only [shearProfile, tail, hp, mul_sub, mul_one, ← mul_assoc, hc, one_mul]

/-- The order-g^2 diagnostic is the imported stripping expression itself,
when evaluated on the specified transport slice and normalized observation. -/
theorem active_stripped_tail (F : Frame labels reference beta gamma)
    (L : OPE.MultiDistribution 1) (t : ℝ) (test : OPE.RelativeTest 1)
    (hF : F.transport t = shear (shearProfile t : ℂ))
    (degree : OPE.dimension (labels 1) = 4)
    (observation : L (OPE.dilateRelative (Real.exp (-t)) test) = 1) :
    strippedMultiPairing F (highChannel L) (Real.exp (-t)) 1
      (fun _ => 1) 1 1 test = (tail t : ℂ) := by
  rw [shear_stripped F L (Real.exp (-t)) test (shearProfile t : ℂ)
    (by simpa only [rgTime_exp_neg] using hF) degree observation]
  exact_mod_cast scaled_shearProfile t

theorem tail_div_gSquared (t : ℝ) (ht : 0 ≤ t) :
    tail t / gSquared t = tailRatio t := by
  have hn : 1 + 2*t ≠ 0 := by linarith
  dsimp [tail, gSquared, tailRatio]
  field_simp

/-- The omitted contribution has leading size g^2, rather than being flat
in every running-coupling order. -/
theorem tailRatio_limit : Filter.Tendsto tailRatio Filter.atTop (nhds 1) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 4 (by norm_num)
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 4 (by norm_num)
  simp only [Real.rpow_zero, one_mul] at h0
  simp only [Real.rpow_one] at h1
  have hd : Filter.Tendsto (fun t : ℝ => (1+2*t)*Real.exp (-4*t))
      Filter.atTop (nhds 0) := by
    convert h0.add (h1.const_mul 2) using 1
    · funext t; ring
    · norm_num
  simpa only [sub_zero, tailRatio] using! Filter.Tendsto.sub
    (tendsto_const_nhds (x := (1 : ℝ))) hd

theorem tail_not_flat :
    ¬ (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ t : ℝ in Filter.atTop,
      ‖tail t‖ ≤ epsilon * gSquared t) := by
  intro h
  have he := h (1/2) (by norm_num)
  have hr : ∀ᶠ t : ℝ in Filter.atTop, tailRatio t ≤ (1/2 : ℝ) := by
    filter_upwards [he, Filter.eventually_ge_atTop (0 : ℝ)] with t hb ht
    rw [← tail_div_gSquared t ht]
    have hg : 0 < gSquared t := inv_pos.mpr (by linarith)
    apply (div_le_iff₀ hg).mpr
    exact (le_abs_self (tail t)).trans (by simpa only [Real.norm_eq_abs] using hb)
  have bad : (1 : ℝ) ≤ 1/2 := le_of_tendsto tailRatio_limit hr
  norm_num at bad

#print axioms highChannel_stripped
#print axioms highChannel_restrict
#print axioms restricted_stripped_zero
#print axioms shear
#print axioms shear_incoming
#print axioms shear_outgoing
#print axioms shear_overlap
#print axioms projection_shear_failure
#print axioms shear_filtered
#print axioms shear_stripped
#print axioms finite_sector_discrepancy
#print axioms shearProfile_initial
#print axioms rgTime_exp_neg
#print axioms shearProfile_derivative
#print axioms scaled_shearProfile
#print axioms active_stripped_tail
#print axioms tail_div_gSquared
#print axioms tailRatio_limit
#print axioms tail_not_flat
end YMYMGAudit
