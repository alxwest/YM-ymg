/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import YangMills.OSRecon.Vendored.Spacetime

/-!
# Vendored from OSreconstruction: conjugation and external tensor product

Upstream: https://github.com/xiyin137/OSreconstruction, local fork
`cherkis/OSreconstruction` at commit `936defd39f199b38301c05e8caeae6b16eb7d167`.

Source: `OSReconstruction/Wightman/SchwartzTensorProduct.lean` 58-91
(`SchwartzMap.conj`, `conj_apply`, `conj_conj`, `seminorm_conj_le`) and 327-470
(`SchwartzMap.tensorProduct`, `tensorProduct_apply`).

Deviations: none in the declarations. The upstream file imports the `Mathlib429Compat`
instance shim; it is not imported here (see `YangMills/OSRecon/README.md`).
-/

noncomputable section

open scoped SchwartzMap
open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Complex Conjugation of Schwartz Functions -/

/-- Complex conjugation of a ℂ-valued Schwartz function.
    If f ∈ S(E, ℂ), then f̄ ∈ S(E, ℂ) where f̄(x) = conj(f(x)).

    This is well-defined because:
    1. conj : ℂ → ℂ is smooth (it's ℝ-linear)
    2. conj preserves norms: ‖conj(z)‖ = ‖z‖
    So f̄ has the same decay bounds as f. -/
def SchwartzMap.conj (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) where
  toFun := fun x => starRingEnd ℂ (f x)
  smooth' := by
    -- conj = Complex.conjCLE is a ContinuousLinearEquiv over ℝ, hence smooth
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp f.smooth'
  decay' := by
    intro k n
    -- Complex conjugation is a linear isometry, so ‖iteratedFDeriv ℝ n (conj ∘ f) x‖ = ‖iteratedFDeriv ℝ n f x‖
    obtain ⟨C, hC⟩ := f.decay' k n
    exact ⟨C, fun x => by
      have := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) f x n
      simp only [Function.comp_def] at this
      -- starRingEnd ℂ and conjLIE are definitionally equal
      have heq : (fun x => (starRingEnd ℂ) (f x)) = (fun x => Complex.conjLIE (f x)) := rfl
      rw [heq, this]; exact hC x⟩

/-- Conjugation preserves the pointwise values. -/
@[simp]
theorem SchwartzMap.conj_apply (f : 𝓢(E, ℂ)) (x : E) :
    f.conj x = starRingEnd ℂ (f x) := rfl

/-- Conjugation is an involution. -/
theorem SchwartzMap.conj_conj (f : 𝓢(E, ℂ)) :
    f.conj.conj = f := by
  ext x
  simp [SchwartzMap.conj_apply]

/-- Complex conjugation does not increase Schwartz seminorms. -/
theorem SchwartzMap.seminorm_conj_le (k n : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℝ k n f.conj ≤ SchwartzMap.seminorm ℝ k n f := by
  refine SchwartzMap.seminorm_le_bound ℝ k n f.conj (by positivity) ?_
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => starRingEnd ℂ (f y)) x‖ ≤
    SchwartzMap.seminorm ℝ k n f
  have heq : (fun y => starRingEnd ℂ (f y)) = fun y => Complex.conjLIE (f y) := rfl
  have hnorm :
      ‖iteratedFDeriv ℝ n (fun y => Complex.conjLIE (f y)) x‖ =
        ‖iteratedFDeriv ℝ n f x‖ :=
    Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) f x n
  rw [heq, hnorm]
  exact SchwartzMap.le_seminorm ℝ k n f x

/-! ### External Tensor Product of Schwartz Functions -/

/-- The external tensor product of two Schwartz functions.

    Given f ∈ S(Fin m → E, ℂ) and g ∈ S(Fin k → E, ℂ), define:
      (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(x_{m+1},...,x_{m+k})

    This is Schwartz because projections are smooth (linear), f and g are smooth,
    multiplication is smooth (bilinear), and the decay bounds combine. -/
def SchwartzMap.tensorProduct {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    𝓢(Fin (m + k) → E, ℂ) where
  toFun := fun x => f (splitFirst m k x) * g (splitLast m k x)
  smooth' := by
    -- f ∘ splitFirst and g ∘ splitLast are smooth (smooth ∘ linear projection)
    -- Their product is smooth (ContDiff.mul)
    apply ContDiff.mul
    · exact f.smooth'.comp (contDiff_pi.mpr fun i =>
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E)
          (Fin.castAdd k i)).contDiff)
    · exact g.smooth'.comp (contDiff_pi.mpr fun j =>
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E)
          (Fin.natAdd m j)).contDiff)
  decay' := by
    intro p l
    -- Smooth factors (for Leibniz rule)
    -- Note: f.smooth' has order ∞ : ℕ∞, which coerces to ↑∞ : WithTop ℕ∞
    have hfs := f.smooth'.comp (splitFirstCLM m k (E := E)).contDiff
    have hgs := g.smooth'.comp (splitLastCLM m k (E := E)).contDiff
    -- Composition norm bounds: ‖D^j(f ∘ π₁) x‖ ≤ ‖D^j f (π₁ x)‖ (since ‖π₁‖ ≤ 1)
    have hcf : ∀ j (x : Fin (m + k) → E),
        ‖iteratedFDeriv ℝ j (f.toFun ∘ splitFirst m k) x‖ ≤
        ‖iteratedFDeriv ℝ j f.toFun (splitFirst m k x)‖ := by
      intro j x
      rw [show f.toFun ∘ splitFirst m k = f.toFun ∘ ↑(splitFirstCLM m k (E := E)) from rfl,
        (splitFirstCLM m k).iteratedFDeriv_comp_right f.smooth' x
          (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => splitFirstCLM_opNorm_le m k)))
    have hcg : ∀ j (x : Fin (m + k) → E),
        ‖iteratedFDeriv ℝ j (g.toFun ∘ splitLast m k) x‖ ≤
        ‖iteratedFDeriv ℝ j g.toFun (splitLast m k x)‖ := by
      intro j x
      rw [show g.toFun ∘ splitLast m k = g.toFun ∘ ↑(splitLastCLM m k (E := E)) from rfl,
        (splitLastCLM m k).iteratedFDeriv_comp_right g.smooth' x
          (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => splitLastCLM_opNorm_le m k)))
    -- Schwartz decay constants (via Choice)
    choose Cf hCf using fun p j => f.decay' p j
    choose Cg hCg using fun p j => g.decay' p j
    -- The total bound constant
    refine ⟨2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i)), fun x => ?_⟩
    -- Step 1: Leibniz rule gives bound on ‖D^l(f⊗g)‖
    have hLeib := norm_iteratedFDeriv_mul_le (n := l) hfs hgs x
      (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
    -- Step 2: Bound ‖x‖^p using norm splitting
    have hnorm_split := norm_le_splitFirst_add_splitLast m k x
    -- Step 3: (a+b)^p ≤ 2^p (a^p + b^p) for a, b ≥ 0
    have add_pow_le : (‖splitFirst m k x‖ + ‖splitLast m k x‖) ^ p ≤
        2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) := by
      have hmax : (max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p ≤
          ‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p := by
        rcases max_cases ‖splitFirst m k x‖ ‖splitLast m k x‖ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
        · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      have h_add_le_2max : ‖splitFirst m k x‖ + ‖splitLast m k x‖ ≤
          2 * max ‖splitFirst m k x‖ ‖splitLast m k x‖ := by
        linarith [le_max_left ‖splitFirst m k x‖ ‖splitLast m k x‖,
                  le_max_right ‖splitFirst m k x‖ ‖splitLast m k x‖]
      calc _ ≤ (2 * max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p :=
            pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
        _ = (2 : ℝ) ^ p * (max ‖splitFirst m k x‖ ‖splitLast m k x‖) ^ p :=
            mul_pow (2 : ℝ) _ p
        _ ≤ 2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) :=
            mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
    -- Step 4: Main calculation
    have h_pow : ‖x‖ ^ p ≤ 2 ^ p * (‖splitFirst m k x‖ ^ p + ‖splitLast m k x‖ ^ p) :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_split _).trans add_pow_le
    -- For each summand, bound using Schwartz decay of f and g
    have h_term : ∀ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖) ≤
        2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
      intro i _
      -- Name the key quantities for readability
      set a := ‖splitFirst m k x‖ with ha_def
      set b := ‖splitLast m k x‖ with hb_def
      set F := ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ with hF_def
      set G := ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖ with hG_def
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := norm_nonneg _
      have hF_nn : 0 ≤ F := norm_nonneg _
      have hG_nn : 0 ≤ G := norm_nonneg _
      -- a^p * F ≤ Cf p i and G ≤ Cg 0 (l-i)
      have hf1 : a ^ p * F ≤ Cf p i := hCf p i (splitFirst m k x)
      have hg1 : G ≤ Cg 0 (l - i) := by
        have := hCg 0 (l - i) (splitLast m k x); simp at this; linarith
      -- F ≤ Cf 0 i and b^p * G ≤ Cg p (l-i)
      have hf2 : F ≤ Cf 0 i := by
        have := hCf 0 i (splitFirst m k x); simp at this; linarith
      have hg2 : b ^ p * G ≤ Cg p (l - i) := hCg p (l - i) (splitLast m k x)
      -- Key: a^p * F * G ≤ Cf(p,i) * Cg(0,l-i)
      have hprod1 : a ^ p * F * G ≤ Cf p i * Cg 0 (l - i) :=
        mul_le_mul hf1 hg1 hG_nn (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
      -- Key: b^p * F * G = F * (b^p * G) ≤ Cf(0,i) * Cg(p,l-i)
      have hprod2 : b ^ p * F * G ≤ Cf 0 i * Cg p (l - i) := by
        calc b ^ p * F * G = F * (b ^ p * G) := by ring
          _ ≤ Cf 0 i * Cg p (l - i) :=
            mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
              (le_trans hF_nn hf2)
      -- Assemble
      have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
      calc ‖x‖ ^ p * (↑(l.choose i) * F * G)
          ≤ (2 ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
            mul_le_mul_of_nonneg_right h_pow
              (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
        _ = 2 ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by ring
        _ ≤ 2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
            exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
    -- Assemble the final bound
    calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
          (fun y => f (splitFirst m k y) * g (splitLast m k y)) x‖
        ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i (f.toFun ∘ splitFirst m k) x‖ *
          ‖iteratedFDeriv ℝ (l - i) (g.toFun ∘ splitLast m k) x‖ := by
          gcongr; exact hLeib
      _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖ := by
          gcongr with i hi
          · exact (hcf i x).trans le_rfl
          · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
          ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (splitFirst m k x)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (splitLast m k x)‖) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          2 ^ p * (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
          exact Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]

/-- The tensor product function at a point. -/
@[simp]
theorem SchwartzMap.tensorProduct_apply {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ))
    (x : Fin (m + k) → E) :
    f.tensorProduct g x = f (splitFirst m k x) * g (splitLast m k x) := rfl

end
