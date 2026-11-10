import TargetKernel

/-! E0 on the actual OSreconstruction zero-diagonal Schwartz test space.
The argument instantiates the group's diagonal-flat Taylor estimate directly
in its sup-norm coordinates. Constants are allowed to depend on arity. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory YangMills.Analysis Set Filter
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

def schwinger : SchwingerFunctions 3 := fun n f =>
  ∫ x : NPointDomain 3 n, (targetKernel F n x : ℂ) * f.1 x

theorem schwinger_integrable_bound (n : ℕ) :
    ∃ L : ℕ, ∃ M : ℝ, ∀ f : ZeroDiagonalSchwartz 3 n,
      Integrable (fun x : NPointDomain 3 n => (targetKernel F n x : ℂ) * f.1 x) ∧
      ‖schwinger F n f‖ ≤ M * (Finset.Iic (L, L)).sup
        (schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ) f.1 := by
  obtain ⟨N, hN, B, hB, hK⟩ := targetKernel_bound F n
  let L := max (5 * n) N
  refine ⟨L, B * 2 ^ (5 * n + L) *
    (∫ x : SpacetimeDim 3, EuclideanField.centerWeight 5 x) ^ n, ?_⟩
  intro f
  have hb := integrable_smul_and_norm_integral_le_of_affine_flat (𝕜 := ℝ)
    f.1 N 5 L hN (by simp [L])
    (le_max_right _ _) (by simp [SpacetimeDim])
    (coincidencePairs n) (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun _ _ => 0)
    (fun j _ a p hp he => f.2 j a
      ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, by simpa using he⟩)
    (targetKernel F n) hB
    (fun x hx => hK x (fun i j hij => by
      by_contra hne
      exact hx (i, j) (by simp [coincidencePairs, hne]) (by simpa using hij)))
    ((targetKernel_measurable F n).stronglyMeasurable.smul
      f.1.continuous.stronglyMeasurable).aestronglyMeasurable
  have hs : (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2
      (E := NPointDomain 3 n) (F := ℂ)) =
      schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ := by rfl
  rw [hs] at hb
  simpa only [Complex.real_smul, volume_pi, Fintype.card_fin,
    schwinger, mul_assoc, mul_left_comm, mul_comm] using hb

theorem schwinger_integrable (n : ℕ) (f : ZeroDiagonalSchwartz 3 n) :
    Integrable (fun x : NPointDomain 3 n => (targetKernel F n x : ℂ) * f.1 x) := by
  obtain ⟨L, M, h⟩ := schwinger_integrable_bound F n
  exact (h f).1

theorem E0_linear (n : ℕ) : IsLinearMap ℂ (schwinger F n) where
  map_add f g := by
    change (∫ x, (targetKernel F n x : ℂ) * (f.1 x + g.1 x)) = _
    simp_rw [mul_add]
    exact integral_add (schwinger_integrable F n f) (schwinger_integrable F n g)
  map_smul c f := by
    change (∫ x, (targetKernel F n x : ℂ) * (c * f.1 x)) = c * _
    simp_rw [mul_left_comm (targetKernel F n _ : ℂ) c]
    exact integral_const_mul c _

def schwingerLinear (n : ℕ) : ZeroDiagonalSchwartz 3 n →ₗ[ℂ] ℂ where
  toFun := schwinger F n
  map_add' := (E0_linear F n).map_add
  map_smul' := (E0_linear F n).map_smul

theorem E0_tempered (n : ℕ) : Continuous (schwinger F n) := by
  letI : AddCommGroup (ZeroDiagonalSchwartz 3 n) :=
    inferInstanceAs (AddCommGroup (zeroDiagonalSubmodule 3 n))
  letI : IsTopologicalAddGroup (ZeroDiagonalSchwartz 3 n) :=
    inferInstanceAs (IsTopologicalAddGroup (zeroDiagonalSubmodule 3 n))
  obtain ⟨L, M, h⟩ := schwinger_integrable_bound F n
  let T := schwingerLinear F n
  change Continuous T
  apply continuous_of_continuousAt_zero T
  change Tendsto T (𝓝 0) (𝓝 (T 0))
  rw [T.map_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun f => norm_nonneg (T f)) (fun f => (h f).2)
  have hc : Continuous (fun f : ZeroDiagonalSchwartz 3 n => M *
      (Finset.Iic (L, L)).sup (schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ) f.1) := by
    apply Continuous.const_mul
    apply Continuous.comp _ continuous_subtype_val
    exact Seminorm.continuous_finsetSup fun p _ =>
      (schwartz_withSeminorms ℝ (NPointDomain 3 n) ℂ).continuous_seminorm p
  simpa only [show (0 : ZeroDiagonalSchwartz 3 n).1 = 0 from rfl, map_zero, mul_zero]
    using (hc.continuousAt (x := (0 : ZeroDiagonalSchwartz 3 n))).tendsto

/-- The functional is the genuine absolutely convergent kernel pairing. -/
def schwingerCLM (n : ℕ) : ZeroDiagonalSchwartz 3 n →L[ℂ] ℂ where
  toLinearMap := schwingerLinear F n
  cont := E0_tempered F n

#print axioms schwinger_integrable
#print axioms E0_linear
#print axioms E0_tempered
/-- Identification with the original complex-valued selected correlations,
including all coincidence configurations because the target test vanishes there. -/
theorem schwinger_eq_selected_integral (n : ℕ) (f : ZeroDiagonalSchwartz 3 n) :
    schwinger F n f = ∫ x : NPointDomain 3 n,
      scalarKernel F n (configEquiv n x) * f.1 x := by
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : Function.Injective x
  · rw [targetKernel_eq F x hx]
  · have hcoin : x ∈ CoincidenceLocus 3 n := by
      simp only [Function.Injective] at hx
      push Not at hx
      obtain ⟨i, j, heq, hne⟩ := hx
      exact ⟨i, j, hne, heq⟩
    have hz : f.1 x = 0 := by
      apply norm_eq_zero.mp
      have h := congrArg norm (f.2 0 x hcoin)
      simpa only [norm_iteratedFDeriv_zero, norm_zero] using h
    simp only [hz, mul_zero]

end YMOSBridge
