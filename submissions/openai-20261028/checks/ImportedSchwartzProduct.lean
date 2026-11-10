import ImportedSchwartzDomain
import Mathlib.Tactic.GCongr

noncomputable section
open scoped SchwartzMap BigOperators Topology
open Finset
set_option maxHeartbeats 500000

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite Schwartz seminorm envelope used for the external-product estimate. -/
def productSeminorm (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] (k m : ℕ) :
    Seminorm ℂ 𝓢(D, ℂ) :=
  ({k, 0} ×ˢ Icc 0 m).sup (schwartzSeminormFamily ℂ D ℂ)

theorem continuous_productSeminorm (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    (k m : ℕ) : Continuous (productSeminorm D k m) :=
  Seminorm.continuous_finsetSup
    (fun i _ => (schwartz_withSeminorms ℂ D ℂ).continuous_seminorm i)

private theorem seminorm_le_productSeminorm (f : 𝓢(E, ℂ)) (k m c : ℕ) (hc : c ≤ m) :
    SchwartzMap.seminorm ℂ k c f ≤ productSeminorm E k m f ∧
      SchwartzMap.seminorm ℂ 0 c f ≤ productSeminorm E k m f := by
  constructor
  · change (schwartzSeminormFamily ℂ E ℂ (k, c)) f ≤
      (({k, 0} ×ˢ Icc 0 m).sup (schwartzSeminormFamily ℂ E ℂ)) f
    exact Seminorm.le_def.mp (Finset.le_sup
      (show (k, c) ∈ ({k, 0} ×ˢ Icc 0 m : Finset (ℕ × ℕ)) from by simp [hc])) f
  · change (schwartzSeminormFamily ℂ E ℂ (0, c)) f ≤
      (({k, 0} ×ˢ Icc 0 m).sup (schwartzSeminormFamily ℂ E ℂ)) f
    exact Seminorm.le_def.mp (Finset.le_sup
      (show (0, c) ∈ ({k, 0} ×ˢ Icc 0 m : Finset (ℕ × ℕ)) from by simp [hc])) f

private theorem norm_iteratedFDeriv_comp_contract (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (f : 𝓢(F, ℂ)) (c : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ c (fun x => f (L x)) x‖ ≤ ‖iteratedFDeriv ℝ c f (L x)‖ := by
  change ‖iteratedFDeriv ℝ c (f.toFun ∘ ⇑L) x‖ ≤ ‖iteratedFDeriv ℝ c f.toFun (L x)‖
  rw [L.iteratedFDeriv_comp_right f.smooth' x (i := c)
    (show (↑↑c : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from by exact_mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ c f.toFun (L x)‖ * ∏ _ : Fin c, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ _ * 1 := by
      gcongr
      exact prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
    _ = _ := mul_one _

private theorem weighted_derivative_externalProduct_le
    (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (k m : ℕ) (x : E × F) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x : E × F => f x.1 * g x.2) x‖ ≤
      2 ^ m * (productSeminorm E k m f * productSeminorm F k m g) := by
  let P := productSeminorm E k m f
  let Q := productSeminorm F k m g
  have hf (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (fun x : E × F => f x.1) x‖ ≤ P ∧
      ‖x.1‖ ^ k * ‖iteratedFDeriv ℝ i (fun x : E × F => f x.1) x‖ ≤ P := by
    have hb := norm_iteratedFDeriv_comp_contract (ContinuousLinearMap.fst ℝ E F)
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_fst_le x)) f i x
    exact ⟨(hb.trans (norm_iteratedFDeriv_le_seminorm ℂ f i x.1)).trans
        (seminorm_le_productSeminorm f k m i hi).2,
      ((mul_le_mul_of_nonneg_left hb (by positivity)).trans (le_seminorm ℂ k i f x.1)).trans
        (seminorm_le_productSeminorm f k m i hi).1⟩
  have hg (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (fun x : E × F => g x.2) x‖ ≤ Q ∧
      ‖x.2‖ ^ k * ‖iteratedFDeriv ℝ i (fun x : E × F => g x.2) x‖ ≤ Q := by
    have hb := norm_iteratedFDeriv_comp_contract (ContinuousLinearMap.snd ℝ E F)
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_snd_le x)) g i x
    exact ⟨(hb.trans (norm_iteratedFDeriv_le_seminorm ℂ g i x.2)).trans
        (seminorm_le_productSeminorm g k m i hi).2,
      ((mul_le_mul_of_nonneg_left hb (by positivity)).trans (le_seminorm ℂ k i g x.2)).trans
        (seminorm_le_productSeminorm g k m i hi).1⟩
  have hterm (i : ℕ) (hi : i ≤ m) :
      ‖x‖ ^ k * (‖iteratedFDeriv ℝ i (fun x : E × F => f x.1) x‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun x : E × F => g x.2) x‖) ≤ P * Q := by
    rw [Prod.norm_def]
    rcases le_total ‖x.1‖ ‖x.2‖ with hx | hx
    · rw [max_eq_right hx, mul_left_comm]
      exact mul_le_mul (hf i hi).1 (hg (m - i) (Nat.sub_le ..)).2 (by positivity)
        (apply_nonneg (productSeminorm E k m) f)
    · rw [max_eq_left hx, ← mul_assoc]
      exact mul_le_mul (hf i hi).2 (hg (m - i) (Nat.sub_le ..)).1 (by positivity)
        (apply_nonneg (productSeminorm E k m) f)
  have hfS := f.smooth'.comp (ContinuousLinearMap.fst ℝ E F).contDiff
  have hgS := g.smooth'.comp (ContinuousLinearMap.snd ℝ E F).contDiff
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : E × F => f x.1) x‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun x : E × F => g x.2) x‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hfS hgS x (by exact_mod_cast le_top))
        (by positivity)
    _ = ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (‖x‖ ^ k *
        (‖iteratedFDeriv ℝ i (fun x : E × F => f x.1) x‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun x : E × F => g x.2) x‖)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (P * Q) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hterm i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
        (Nat.cast_nonneg _)
    _ = (∑ i ∈ range (m + 1), (m.choose i : ℝ)) * (P * Q) := (sum_mul ..).symm
    _ = _ := by norm_cast; rw [Nat.sum_range_choose]

/-- The external product on two possibly different real normed domains. -/
def externalProduct (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) : 𝓢(E × F, ℂ) where
  toFun x := f x.1 * g x.2
  smooth' := (f.smooth'.comp (ContinuousLinearMap.fst ℝ E F).contDiff).mul
    (g.smooth'.comp (ContinuousLinearMap.snd ℝ E F).contDiff)
  decay' k m := ⟨_, weighted_derivative_externalProduct_le f g k m⟩

@[simp] theorem externalProduct_apply (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (x : E × F) :
    externalProduct f g x = f x.1 * g x.2 := rfl

theorem seminorm_externalProduct_le (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (k m : ℕ) :
    SchwartzMap.seminorm ℂ k m (externalProduct f g) ≤
      2 ^ m * (productSeminorm E k m f * productSeminorm F k m g) :=
  seminorm_le_bound ℂ k m _ (by positivity) (weighted_derivative_externalProduct_le f g k m)

@[simp] theorem externalProduct_add_left (f f' : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    externalProduct (f + f') g = externalProduct f g + externalProduct f' g := by
  ext x; simp [add_mul]

@[simp] theorem externalProduct_add_right (f : 𝓢(E, ℂ)) (g g' : 𝓢(F, ℂ)) :
    externalProduct f (g + g') = externalProduct f g + externalProduct f g' := by
  ext x; simp [mul_add]

@[simp] theorem externalProduct_smul_left (c : ℂ) (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    externalProduct (c • f) g = c • externalProduct f g := by
  ext x; simp [smul_eq_mul, mul_assoc]

@[simp] theorem externalProduct_smul_right (c : ℂ) (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    externalProduct f (c • g) = c • externalProduct f g := by
  ext x; simp [smul_eq_mul]; ring

theorem continuous_externalProduct :
    Continuous (fun fg : 𝓢(E, ℂ) × 𝓢(F, ℂ) => externalProduct fg.1 fg.2) := by
  rw [continuous_iff_continuousAt]
  intro fg
  rw [ContinuousAt, (schwartz_withSeminorms ℂ (E × F) ℂ).tendsto_nhds]
  rintro ⟨k, m⟩ ε hε
  let P := productSeminorm E k m
  let Q := productSeminorm F k m
  let B (uv : 𝓢(E, ℂ) × 𝓢(F, ℂ)) :=
    2 ^ m * (P (uv.1 - fg.1) * Q uv.2) + 2 ^ m * (P fg.1 * Q (uv.2 - fg.2))
  have hP := continuous_productSeminorm E k m
  have hQ := continuous_productSeminorm F k m
  have hB : Continuous B :=
    (continuous_const.mul ((hP.comp (continuous_fst.sub continuous_const)).mul
      (hQ.comp continuous_snd))).add
      (continuous_const.mul (continuous_const.mul (hQ.comp (continuous_snd.sub continuous_const))))
  have hB0 : B fg = 0 := by simp [B]
  filter_upwards [(hB.tendsto' fg 0 hB0).eventually_lt_const hε] with uv huv
  apply lt_of_le_of_lt _ huv
  have heq : externalProduct uv.1 uv.2 - externalProduct fg.1 fg.2 =
      externalProduct (uv.1 - fg.1) uv.2 + externalProduct fg.1 (uv.2 - fg.2) := by
    ext x; simp; ring
  change SchwartzMap.seminorm ℂ k m _ ≤ _
  rw [heq]
  exact (map_add_le_add _ _ _).trans (add_le_add
    (seminorm_externalProduct_le _ _ k m) (seminorm_externalProduct_le _ _ k m))

/-- For each fixed right factor, external multiplication is a complex CLM. -/
def externalProductLeftCLM (g : 𝓢(F, ℂ)) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E × F, ℂ) where
  toFun f := externalProduct f g
  map_add' f f' := externalProduct_add_left f f' g
  map_smul' c f := externalProduct_smul_left c f g
  cont := continuous_externalProduct.comp (continuous_id.prodMk continuous_const)

/-- For each fixed left factor, external multiplication is a complex CLM. -/
def externalProductRightCLM (f : 𝓢(E, ℂ)) : 𝓢(F, ℂ) →L[ℂ] 𝓢(E × F, ℂ) where
  toFun g := externalProduct f g
  map_add' g g' := externalProduct_add_right f g g'
  map_smul' c g := externalProduct_smul_right c f g
  cont := continuous_externalProduct.comp (continuous_const.prodMk continuous_id)

theorem externalProduct_assoc {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (h : 𝓢(G, ℂ)) :
    complexDomCongr (ContinuousLinearEquiv.prodAssoc ℝ E F G)
      (externalProduct f (externalProduct g h)) = externalProduct (externalProduct f g) h := by
  ext x
  simp [mul_assoc]

theorem externalProduct_conjugate (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    postcompCLM Complex.conjCLE.toContinuousLinearMap (externalProduct f g) =
      externalProduct (postcompCLM Complex.conjCLE.toContinuousLinearMap f)
        (postcompCLM Complex.conjCLE.toContinuousLinearMap g) := by
  ext x
  simp

theorem support_externalProduct (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    Function.support (externalProduct f g : E × F → ℂ) =
      Function.support (f : E → ℂ) ×ˢ Function.support (g : F → ℂ) := by
  ext x
  simp [Function.mem_support]

theorem tsupport_externalProduct (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    tsupport (externalProduct f g : E × F → ℂ) =
      tsupport (f : E → ℂ) ×ˢ tsupport (g : F → ℂ) := by
  simp only [tsupport, support_externalProduct, closure_prod_eq]

end SchwartzMap

namespace EuclideanField

/-- Split a tuple into its initial and final blocks, with its product topology. -/
def appendDomainEquiv (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] (r s : ℕ) :
    (Fin (r + s) → D) ≃L[ℝ] (Fin r → D) × (Fin s → D) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (r + s) => D)
    finSumFinEquiv).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin r) (Fin s) (fun _ => D))

@[simp] theorem appendDomainEquiv_apply (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    (r s : ℕ) (x : Fin (r + s) → D) :
    appendDomainEquiv D r s x =
      (fun i => x (Fin.castAdd s i), fun i => x (Fin.natAdd r i)) := rfl

end EuclideanField
