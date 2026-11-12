import YangMills.FilteredQuantumRG

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
Metamorphic checks of the imported finite-sector definitions. Reordering
labels changes all matrix and coefficient indices together. This tests the
actual Frame and stripping formula; it does not construct a physical model
or prove covariance under every finite renormalization.
-/

noncomputable section
open scoped BigOperators
namespace YMYMG.BasisAudit
open YangMills YangMills.PerturbativeFlow YangMills.FilteredRG

def coordinates {m : ℕ} (sigma : Equiv.Perm (Fin m)) :
    (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) where
  toFun v i := v (sigma i)
  invFun v i := v (sigma.symm i)
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := rfl
  map_smul' c v := rfl

theorem coordinates_symm_single {m : ℕ} (sigma : Equiv.Perm (Fin m))
    (j : Fin m) (a : ℂ) :
    (coordinates sigma).symm (Pi.single j a) = Pi.single (sigma j) a := by
  classical
  ext i
  simp [coordinates, Pi.single_apply, Equiv.symm_apply_eq]

def conjugate {m : ℕ} (sigma : Equiv.Perm (Fin m))
    (R : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ)) :
    (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) :=
  (coordinates sigma).symm.trans (R.trans (coordinates sigma))

theorem conjugate_entry {m : ℕ} (sigma : Equiv.Perm (Fin m))
    (R : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ)) (i j : Fin m) :
    conjugate sigma R (Pi.single j 1) i = R (Pi.single (sigma j) 1) (sigma i) := by
  simp only [conjugate, LinearEquiv.trans_apply, coordinates_symm_single]
  rfl

theorem conjugate_symm_entry {m : ℕ} (sigma : Equiv.Perm (Fin m))
    (R : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ)) (i j : Fin m) :
    (conjugate sigma R).symm (Pi.single j 1) i =
      R.symm (Pi.single (sigma j) 1) (sigma i) := by
  change conjugate sigma R.symm (Pi.single j 1) i = _
  exact conjugate_entry sigma R.symm i j

variable {G : CompactSimpleGaugeGroup} {m : ℕ}
  {labels : Fin m → InvariantInsertionLabel G}
  {reference : RenormalizationScale} {beta : ℕ → ℝ}
  {gamma : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}

def reindexFrame (sigma : Equiv.Perm (Fin m))
    (F : Frame labels reference beta gamma) :
    Frame (fun i => labels (sigma i)) reference beta
      (fun mu order i j => gamma mu order (sigma i) (sigma j)) where
  running := F.running
  gamma mu g i j := F.gamma mu g (sigma i) (sigma j)
  gamma_smooth i j := F.gamma_smooth (sigma i) (sigma j)
  gamma_jet mu i j := F.gamma_jet mu (sigma i) (sigma j)
  transport t := conjugate sigma (F.transport t)
  initial v := by
    ext i
    change F.transport 0 ((coordinates sigma).symm v) (sigma i) = v i
    rw [F.initial]
    simp [coordinates]
  filtered t i j h := by
    rw [conjugate_entry]
    exact F.filtered t (sigma i) (sigma j) h
  equation t i j ht := by
    simp only [conjugate_entry]
    rw [Equiv.sum_comp sigma (fun k =>
      F.gamma (runningScale reference t) (F.running.coupling t) (sigma i) k *
        F.transport t (Pi.single (sigma j) 1) k)]
    exact F.equation t (sigma i) (sigma j) ht

abbrev Coefficients (m : ℕ) :=
  (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n

def reindexCoefficients (sigma : Equiv.Perm (Fin m)) (C : Coefficients m) :
    Coefficients m :=
  fun n inputs last output => C n (fun r => sigma (inputs r)) (sigma last) (sigma output)

theorem stripping_reindex (sigma : Equiv.Perm (Fin m))
    (F : Frame labels reference beta gamma) (C : Coefficients m)
    (scale : ℝ) (n : ℕ) (inputs : Fin n → Fin m) (last output : Fin m)
    (test : OPE.RelativeTest n) :
    strippedMultiPairing (reindexFrame sigma F) (reindexCoefficients sigma C)
      scale n inputs last output test =
    strippedMultiPairing F C scale n (fun r => sigma (inputs r))
      (sigma last) (sigma output) test := by
  classical
  simp only [strippedMultiPairing, reindexFrame, reindexCoefficients,
    conjugate_entry, conjugate_symm_entry]
  refine Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin n => sigma)) _ _ ?_
  intro xs
  refine Fintype.sum_equiv sigma _ _ ?_
  intro j
  refine Fintype.sum_equiv sigma _ _ ?_
  intro k
  rfl

theorem all_orders_reindex (sigma : Equiv.Perm (Fin m))
    (F : Frame labels reference beta gamma) (C : Coefficients m)
    (physical : ℕ → Coefficients m)
    (h : AllOrderMultiMatch F C physical) :
    AllOrderMultiMatch (reindexFrame sigma F) (reindexCoefficients sigma C)
      (fun order => reindexCoefficients sigma (physical order)) := by
  refine ⟨fun n inputs last output => h.1 n _ _ _,
    fun order n inputs last output => h.2.1 order n _ _ _, ?_⟩
  intro n hn inputs last output test hTest N epsilon hEpsilon
  obtain ⟨delta, hDelta, hOne, hBound⟩ :=
    h.2.2 n hn (fun r => sigma (inputs r)) (sigma last) (sigma output)
      test hTest N epsilon hEpsilon
  refine ⟨delta, hDelta, hOne, fun scale hScale hSmall => ?_⟩
  rw [stripping_reindex]
  exact hBound scale hScale hSmall

/-- Reordering is an equivalence, including locality and every remainder bound. -/
theorem all_orders_reindex_iff (sigma : Equiv.Perm (Fin m))
    (F : Frame labels reference beta gamma) (C : Coefficients m)
    (physical : ℕ → Coefficients m) :
    AllOrderMultiMatch (reindexFrame sigma F) (reindexCoefficients sigma C)
      (fun order => reindexCoefficients sigma (physical order)) ↔
    AllOrderMultiMatch F C physical := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro n inputs last output
      simpa only [reindexCoefficients, Equiv.apply_symm_apply] using
        h.1 n (fun r => sigma.symm (inputs r)) (sigma.symm last) (sigma.symm output)
    · intro order n inputs last output
      simpa only [reindexCoefficients, Equiv.apply_symm_apply] using
        h.2.1 order n (fun r => sigma.symm (inputs r)) (sigma.symm last)
          (sigma.symm output)
    · intro n hn inputs last output test hTest N epsilon hEpsilon
      obtain ⟨delta, hDelta, hOne, hBound⟩ :=
        h.2.2 n hn (fun r => sigma.symm (inputs r)) (sigma.symm last)
          (sigma.symm output) test hTest N epsilon hEpsilon
      refine ⟨delta, hDelta, hOne, fun scale hScale hSmall => ?_⟩
      have hb := hBound scale hScale hSmall
      simp only [stripping_reindex, reindexCoefficients, Equiv.apply_symm_apply] at hb
      exact hb
  · exact all_orders_reindex sigma F C physical

#print axioms coordinates_symm_single
#print axioms conjugate_entry
#print axioms conjugate_symm_entry
#print axioms reindexFrame
#print axioms stripping_reindex
#print axioms all_orders_reindex
#print axioms all_orders_reindex_iff

end YMYMG.BasisAudit
