import Temperedness

/-! A translation-independent majorant for a fixed joint Schwartz test.
Flatness is required precisely on the translated coincidence loci. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory YangMills.Analysis Set Filter
open scoped Topology BigOperators

theorem separation_translate {n : ℕ} (b x : NPointDomain 3 n) :
    separation (x + b) = affineCoincidenceSeparation (coincidencePairs n)
      (fun i j => b j - b i) x := by
  classical
  have he (p : Fin n × Fin n) :
      ‖(x+b) p.1 - ((x+b) p.2 + 0)‖ =
        ‖x p.1 - (x p.2 + (b p.2 - b p.1))‖ := by
    congr 1
    simp only [Pi.add_apply, add_zero]
    abel
  simp only [separation, affineCoincidenceSeparation, he]

theorem translated_flat {n : ℕ} (f : SchwartzNPoint 3 n)
    (h : ZeroDiagonalSchwartz 3 n) (b : NPointDomain 3 n)
    (hf : ∀ x, f x = h.1 (x + b)) (j : ℕ) (x : NPointDomain 3 n)
    (p : Fin n × Fin n) (hp : p ∈ coincidencePairs n)
    (he : x p.1 = x p.2 + (b p.2 - b p.1)) :
    iteratedFDeriv ℝ j f x = 0 := by
  have hh : (x+b) p.1 = (x+b) p.2 := by
    simp only [Pi.add_apply, he]
    abel
  rw [show (f : NPointDomain 3 n → ℂ) = (fun x => h.1 (x+b)) from funext hf,
    iteratedFDeriv_comp_add_right]
  exact h.2 j (x+b) ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, hh⟩

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- The bound depends on f, but not on the displacement b or the flat witness h. -/
theorem translated_kernel_majorant (n : ℕ) (f : SchwartzNPoint 3 n) :
    ∃ D : ℝ, 0 ≤ D ∧
      Integrable (fun x : NPointDomain 3 n =>
        D * ∏ i, EuclideanField.centerWeight 5 (x i)) ∧
      ∀ (b : NPointDomain 3 n) (h : ZeroDiagonalSchwartz 3 n),
        (∀ x, f x = h.1 (x+b)) → ∀ x : NPointDomain 3 n,
        ‖(targetKernel F n (x+b) : ℂ) * f x‖ ≤
          D * ∏ i, EuclideanField.centerWeight 5 (x i) := by
  obtain ⟨N, hN, B, hB, hK⟩ := targetKernel_bound F n
  let L := max (5*n) N
  let D := B * 2 ^ (5*n+L) * (Finset.Iic (L,L)).sup
    (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) f
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hB (by positivity)) (apply_nonneg _ _)
  refine ⟨D, hD, ?_, ?_⟩
  · have hW := EuclideanField.integrable_centerWeight (E := SpacetimeDim 3) 5
      (by simp [SpacetimeDim])
    simpa only [volume_pi] using (Integrable.fintype_prod (fun _ : Fin n => hW)).const_mul D
  · intro b h hf x
    have hclear (x : NPointDomain 3 n)
        (hx : ∀ p ∈ coincidencePairs n, x p.1 ≠ x p.2 + (b p.2 - b p.1)) :
        Function.Injective (x+b) := by
      intro i j hij
      by_contra hne
      apply hx (i,j) (by simp [coincidencePairs, hne])
      have hh : x i + b i = x j + b j := hij
      calc
        x i = (x i+b i)-b i := (add_sub_cancel_right _ _).symm
        _ = (x j+b j)-b i := by rw [hh]
        _ = x j + (b j-b i) := by abel
    have hb := norm_smul_le_prod_centerWeight_of_affine_flat (𝕜 := ℝ)
      f N 5 L hN (by simp [L]) (le_max_right _ _)
      (coincidencePairs n) (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun i j => b j-b i)
      (fun j _ x p hp he => translated_flat f h b hf j x p hp he)
      (fun x => targetKernel F n (x+b)) hB
      (fun x hx => by simpa only [separation_translate] using hK (x+b) (hclear x hx)) x
    simpa only [Complex.real_smul, Fintype.card_fin, D] using hb

#print axioms translated_kernel_majorant
end YMOSBridge
