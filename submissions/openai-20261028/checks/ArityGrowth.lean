import Invariance
import YangMills.OSRecon.Growth
import YM.Work.B11

/-! Corrected OS-II E0′ for the same selected centered trace.

The submission's `YM.Work.B11.phase_cap`, unlike its per-arity `Capped`
interface, retains constants uniform in the number of insertions. This
module transports that bound and uses the group's diagonal-flat estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory YangMills.Analysis
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- One pair of constants works for all arities of the fixed observable. -/
theorem scalarKernel_all_arity_bound :
    ∃ K : ℝ, ∃ A : ℕ, 0 < K ∧
      ∀ (n : ℕ) (r : ℝ), 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x →
        ‖scalarKernel F n x‖ ≤ K ^ n * ((n : ℝ) / r) ^ (A * n) := by
  let v := S.representative 4 (Trace.traceField F)
  obtain ⟨K, A, hK, hb⟩ := Work.B11.phase_cap F.α.space
    F.phase.phase.lengths.cap 4 ‖v‖
  refine ⟨K, A, hK, ?_⟩
  intro n r hr hr1 x hx
  let t : Fin n → C.book.Token := fun _ => ⟨4, v⟩
  have ht : OS.constrained 4 ‖v‖ (Word.realize t x) := by
    intro u hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact ⟨le_refl _, le_refl _⟩
  have hs : spaced r (Word.positions (Word.realize t x)) := by
    let e := finCongr (by simp [Word.realize] : (Word.realize t x).length = n)
    have he (i) : Word.positions (Word.realize t x) i = x (e i) := by
      simp [Word.positions, Word.realize, e]
      rfl
    intro i j hij
    rw [he, he]
    exact hx _ _ (e.injective.ne hij)
  have h := hb F.α.atPoint (Trace.state F) (F.phase.phase.chosen F.α.atPoint)
    _ ht r hr hr1 hs
  rw [Table.readAt] at h
  simpa only [OS.Spread.radius, Word.realize, List.length_ofFn,
    scalarKernel, Table.useAt, Table.classMoment, Table.read, t, v,
    MultilinearMap.compLinearMap_apply]
    using h

/-- A linearly growing singular order, with the explicit n^(A*n) cost. -/
theorem targetKernel_all_arity_bound :
    ∃ K : ℝ, ∃ A : ℕ, 0 < K ∧
      ∀ (n : ℕ) (x : NPointDomain 3 n), Function.Injective x →
        ‖targetKernel F n x‖ ≤
          (K ^ n * (n : ℝ) ^ (A * n)) * (separation x ^ ((A + 1) * n))⁻¹ := by
  obtain ⟨K, A, hK, hb⟩ := scalarKernel_all_arity_bound F
  refine ⟨K, A, hK, ?_⟩
  intro n x hx
  have hδ := separation_positive x hx
  have hδ1 := separation_le_one x
  have h := hb n (separation x) hδ hδ1 _ (separation_spaced x)
  calc
    ‖targetKernel F n x‖ = ‖scalarKernel F n (configEquiv n x)‖ := by
      rw [← targetKernel_eq F x hx, Complex.norm_real]
    _ ≤ K ^ n * ((n : ℝ) / separation x) ^ (A * n) := h
    _ = (K ^ n * (n : ℝ) ^ (A * n)) * (separation x)⁻¹ ^ (A * n) := by
      rw [div_eq_mul_inv, mul_pow, mul_assoc]
    _ ≤ (K ^ n * (n : ℝ) ^ (A * n)) * (separation x)⁻¹ ^ ((A + 1) * n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ ((one_le_inv₀ hδ).mpr hδ1) (Nat.mul_le_mul_right n (by omega))
    _ = _ := by rw [inv_pow]

/-- The elementary factorial estimate absorbs the explicit arity cost. -/
theorem arity_power_le_factorial (A n : ℕ) :
    (n : ℝ) ^ (A * n) ≤ Real.exp A ^ n * (n.factorial : ℝ) ^ A := by
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have h' : (n : ℝ) ^ n ≤ Real.exp n * n.factorial := by
    rwa [div_le_iff₀ hfac] at h
  calc
    (n : ℝ) ^ (A * n) = ((n : ℝ) ^ n) ^ A := by rw [mul_comm, pow_mul]
    _ ≤ (Real.exp n * n.factorial) ^ A := pow_le_pow_left₀ (by positivity) h' A
    _ = Real.exp A ^ n * (n.factorial : ℝ) ^ A := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 2
      ring

/-- E0′ as an estimate, independent of the still-open E4 obligation.
The prefactor alpha can be taken to be one; both the seminorm slope and
factorial exponent are fixed independently of arity. -/
theorem E0_prime_growth :
    ∃ s : ℕ, ∃ β : ℝ, ∃ A : ℕ, 0 < β ∧
      ∀ (n : ℕ) (f : ZeroDiagonalSchwartz 3 n),
        ‖schwinger F n f‖ ≤ β ^ n * (n.factorial : ℝ) ^ A *
          (Finset.Iic (n * s, n * s)).sup
            (schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ) f.1 := by
  obtain ⟨K, A, hK, hb⟩ := targetKernel_all_arity_bound F
  let s := max 5 (A + 1)
  let W : ℝ := ∫ x : SpacetimeDim 3, EuclideanField.centerWeight 5 x
  have hW : 0 ≤ W := integral_nonneg fun x => EuclideanField.centerWeight_nonneg 5 x
  let β : ℝ := K * Real.exp A * 2 ^ (5 + s) * (W + 1)
  refine ⟨s, β, A, by dsimp [β]; positivity, ?_⟩
  intro n f
  by_cases hn : n = 0
  · subst n
    rw [normalized_zero]
    have h₀ : ‖f.1 (0 : NPointDomain 3 0)‖ ≤ SchwartzMap.seminorm ℝ 0 0 f.1 := by
      simpa using (SchwartzMap.le_seminorm ℝ 0 0 f.1 (0 : NPointDomain 3 0))
    simp only [Nat.zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, one_mul]
    have hs₀ : SchwartzMap.seminorm ℝ 0 0 f.1 ≤
        (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ (NPointDomain 3 0) ℂ) f.1 := by
      change (schwartzSeminormFamily ℝ (NPointDomain 3 0) ℂ (0, 0)) f.1 ≤ _
      exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ (NPointDomain 3 0) ℂ)
        (s := Finset.Iic (0, 0)) (i := (0, 0)) (x := f.1)
        (Finset.mem_Iic.mpr (le_refl (0, 0)))
    exact h₀.trans hs₀
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hNpos : 0 < (A + 1) * n := Nat.mul_pos (by omega) hnpos
  have hq : 5 * Fintype.card (Fin n) ≤ n * s := by
    simpa [mul_comm] using Nat.mul_le_mul_right n (le_max_left 5 (A + 1))
  have hNs : (A + 1) * n ≤ n * s := by
    simpa [mul_comm] using Nat.mul_le_mul_right n (le_max_right 5 (A + 1))
  have hjoint := integrable_smul_and_norm_integral_le_of_affine_flat (𝕜 := ℝ)
    f.1 ((A + 1) * n) 5 (n * s) hNpos hq hNs (by simp [SpacetimeDim])
    (coincidencePairs n) (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun _ _ => 0)
    (fun j _ a p hp he => f.2 j a
      ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, by simpa using he⟩)
    (targetKernel F n) (by positivity : 0 ≤ K ^ n * (n : ℝ) ^ (A * n))
    (fun x hx => hb n x (fun i j hij => by
      by_contra hne
      exact hx (i, j) (by simp [coincidencePairs, hne]) (by simpa using hij)))
    ((targetKernel_measurable F n).stronglyMeasurable.smul
      f.1.continuous.stronglyMeasurable).aestronglyMeasurable
  have hseminorm : (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2
      (E := NPointDomain 3 n) (F := ℂ)) =
      schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ := by rfl
  rw [hseminorm] at hjoint
  have he : ‖schwinger F n f‖ ≤
      (K ^ n * (n : ℝ) ^ (A * n) * 2 ^ (5 * n + n * s) * W ^ n) *
        (Finset.Iic (n * s, n * s)).sup
          (schwartzSeminormFamily ℝ (NPointDomain 3 n) ℂ) f.1 := by
    simpa only [W, Complex.real_smul, volume_pi, Fintype.card_fin,
      schwinger, mul_assoc, mul_left_comm, mul_comm] using hjoint.2
  refine he.trans (mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _))
  calc
    K ^ n * (n : ℝ) ^ (A * n) * 2 ^ (5 * n + n * s) * W ^ n
        ≤ K ^ n * (Real.exp A ^ n * (n.factorial : ℝ) ^ A) *
            2 ^ (5 * n + n * s) * (W + 1) ^ n := by
          gcongr
          · exact arity_power_le_factorial A n
          · linarith
    _ = β ^ n * (n.factorial : ℝ) ^ A := by
      dsimp [β]
      rw [show 5 * n + n * s = (5 + s) * n by ring, pow_mul]
      simp only [mul_pow]
      ring

#print axioms scalarKernel_all_arity_bound
#print axioms targetKernel_all_arity_bound
#print axioms E0_prime_growth

end YMOSBridge
