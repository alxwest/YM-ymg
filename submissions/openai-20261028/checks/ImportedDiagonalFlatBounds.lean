import ImportedCenterWeights
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex

/-! Arbitrary-order estimates for joint diagonal-flat Schwartz functions. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace YangMills.Analysis

universe u

/-- An arbitrary-order Taylor bound with a coarse constant independent of the order.
The first `N` derivatives vanish at the base point. No compactness or scalar-valued
codomain restriction is needed. -/
theorem norm_le_pow_mul_of_iteratedFDeriv_eq_zero
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : ℕ) {f : E → F} (hf : ContDiff ℝ ∞ f) {a x : E} {C : ℝ}
    (hC : 0 ≤ C)
    (hflat : ∀ j < N, iteratedFDeriv ℝ j f a = 0)
    (hbound : ∀ y ∈ segment ℝ a x, ‖iteratedFDeriv ℝ N f y‖ ≤ C) :
    ‖f x‖ ≤ ‖x - a‖ ^ N * C := by
  induction N generalizing F x with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using
      hbound x (right_mem_segment ℝ a x)
  | succ N ih =>
    have hfa : f a = 0 := by
      apply norm_eq_zero.mp
      have h := congrArg norm (hflat 0 (by omega))
      simpa only [norm_iteratedFDeriv_zero, norm_zero] using h
    have hdiff : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hflat' : ∀ j < N, iteratedFDeriv ℝ j (fderiv ℝ f) a = 0 := by
      intro j hj
      apply norm_eq_zero.mp
      rw [norm_iteratedFDeriv_fderiv, hflat (j + 1) (by omega), norm_zero]
    have hd : ∀ y ∈ segment ℝ a x, ‖fderiv ℝ f y‖ ≤ ‖x - a‖ ^ N * C := by
      intro y hy
      have hybound : ∀ z ∈ segment ℝ a y, ‖iteratedFDeriv ℝ N (fderiv ℝ f) z‖ ≤ C := by
        intro z hz
        rw [norm_iteratedFDeriv_fderiv]
        exact hbound z ((convex_segment a x).segment_subset (left_mem_segment ℝ a x) hy hz)
      apply (ih hdiff hflat' hybound).trans
      apply mul_le_mul_of_nonneg_right _ hC
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_mem_segment hy) N
    have hmain := (convex_segment a x).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hf.differentiable (by simp) |>.differentiableAt)
      hd (left_mem_segment ℝ a x) (right_mem_segment ℝ a x)
    simpa only [hfa, sub_zero, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmain

/-- Schwartz decay weights are comparable along every segment of length at most one. -/
theorem one_add_norm_le_of_mem_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a x y : E} (hax : ‖x - a‖ ≤ 1) (hy : y ∈ segment ℝ a x) :
    1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
  have hyx : ‖x - y‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact (norm_sub_le_of_mem_segment (segment_symm ℝ a x ▸ hy)).trans
      (by simpa only [norm_sub_rev] using hax)
  have hx := norm_le_insert' x y
  nlinarith [norm_nonneg y]

/-- A directed Schwartz-seminorm Taylor estimate. The uniform constant is explicit
and grows only exponentially in the weight and derivative rectangle orders. -/
theorem weighted_norm_le_pow_mul_sup_seminorm_of_flat
    {𝕜 : Type*} [NormedField 𝕜]
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap E F) (N k L : ℕ) (hk : k ≤ L) (hN : N ≤ L)
    {a x : E} (hax : ‖x - a‖ ≤ 1)
    (hflat : ∀ j < N, iteratedFDeriv ℝ j f a = 0) :
    (1 + ‖x‖) ^ k * ‖f x‖ ≤ ‖x - a‖ ^ N *
      (2 ^ (k + L) * (Finset.Iic (L, L)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f) := by
  let P := (Finset.Iic (L, L)).sup
    (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f
  let C := 2 ^ (k + L) * P / (1 + ‖x‖) ^ k
  have hxpos : 0 < (1 + ‖x‖) ^ k := by positivity
  have hP : 0 ≤ P := apply_nonneg _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ y ∈ segment ℝ a x, ‖iteratedFDeriv ℝ N f y‖ ≤ C := by
    intro y hy
    apply (le_div_iff₀ hxpos).mpr
    calc
      ‖iteratedFDeriv ℝ N f y‖ * (1 + ‖x‖) ^ k ≤
          ‖iteratedFDeriv ℝ N f y‖ * (2 * (1 + ‖y‖)) ^ k := by
        gcongr
        exact one_add_norm_le_of_mem_segment hax hy
      _ = 2 ^ k * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ N f y‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ k * (2 ^ L * P) := by
        exact mul_le_mul_of_nonneg_left
          (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (L, L)) hk hN f y) (by positivity)
      _ = 2 ^ (k + L) * P := by rw [pow_add]; ring
  have hb := norm_le_pow_mul_of_iteratedFDeriv_eq_zero N (f.smooth ⊤) hC hflat hbound
  have hb' := mul_le_mul_of_nonneg_left hb hxpos.le
  dsimp only [C] at hb'
  calc
    _ ≤ (1 + ‖x‖) ^ k * (‖x - a‖ ^ N * (2 ^ (k + L) * P / (1 + ‖x‖) ^ k)) := hb'
    _ = ‖x - a‖ ^ N * (2 ^ (k + L) * P) := by field_simp
    _ = _ := rfl

/-- Moving one coordinate to an affine coincidence locus costs exactly the
corresponding affine separation in the joint maximum norm. -/
theorem norm_sub_update_eq
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (X : ι → E) (i : ι) (z : E) :
    ‖X - Function.update X i z‖ = ‖X i - z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  · simpa using
      norm_le_pi_norm (X - Function.update X i z) i

/-- The minimum of one and a finite family's affine pair separations. Empty
families have separation one. Arbitrary shifts include both ordinary and
translated coincidence loci in one uniform analytic statement. -/
def affineCoincidenceSeparation
    {ι E : Type*} [NormedAddCommGroup E]
    (pairs : Finset (ι × ι)) (shift : ι → ι → E) (X : ι → E) : ℝ := by
  classical
  exact (insert 1 (pairs.image fun p => ‖X p.1 - (X p.2 + shift p.1 p.2)‖)).min'
    (by simp)

theorem affineCoincidenceSeparation_le_one
    {ι E : Type*} [NormedAddCommGroup E]
    (pairs : Finset (ι × ι)) (shift : ι → ι → E) (X : ι → E) :
    affineCoincidenceSeparation pairs shift X ≤ 1 := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem affineCoincidenceSeparation_le
    {ι E : Type*} [NormedAddCommGroup E]
    (pairs : Finset (ι × ι)) (shift : ι → ι → E) (X : ι → E)
    {i j : ι} (hij : (i, j) ∈ pairs) :
    affineCoincidenceSeparation pairs shift X ≤ ‖X i - (X j + shift i j)‖ := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩))

theorem affineCoincidenceSeparation_pos
    {ι E : Type*} [NormedAddCommGroup E]
    (pairs : Finset (ι × ι)) (shift : ι → ι → E) (X : ι → E)
    (hX : ∀ p ∈ pairs, X p.1 ≠ X p.2 + shift p.1 p.2) :
    0 < affineCoincidenceSeparation pairs shift X := by
  classical
  have hm := Finset.min'_mem
    (insert 1 (pairs.image fun p => ‖X p.1 - (X p.2 + shift p.1 p.2)‖))
    (by simp)
  change affineCoincidenceSeparation pairs shift X ∈ _ at hm
  rcases Finset.mem_insert.mp hm with h | h
  · rw [h]; norm_num
  · rcases Finset.mem_image.mp h with ⟨p, hp, he⟩
    rw [← he]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hX p hp))

/-- A nearest affine diagonal exists whenever the truncated separation is below
one. Its explicit projection changes only the first coordinate of that pair. -/
theorem exists_affine_coincidence_at_separation
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (pairs : Finset (ι × ι)) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (shift : ι → ι → E) (X : ι → E)
    (hδ : affineCoincidenceSeparation pairs shift X < 1) :
    ∃ (p : ι × ι) (a : ι → E), p ∈ pairs ∧
      a p.1 = a p.2 + shift p.1 p.2 ∧
      ‖X - a‖ = affineCoincidenceSeparation pairs shift X := by
  classical
  have hm := Finset.min'_mem
    (insert 1 (pairs.image fun p => ‖X p.1 - (X p.2 + shift p.1 p.2)‖))
    (by simp)
  change affineCoincidenceSeparation pairs shift X ∈ _ at hm
  rcases Finset.mem_insert.mp hm with h | h
  · exact False.elim ((ne_of_lt hδ) h)
  · rcases Finset.mem_image.mp h with ⟨p, hp, he⟩
    refine ⟨p, Function.update X p.1 (X p.2 + shift p.1 p.2), hp, ?_, ?_⟩
    · simp [Function.update_of_ne (hne p hp).symm]
    · rw [norm_sub_update_eq, he]

/-- Inverse powers of the least affine separation are cancelled by joint
flatness. The `δ = 1` branch uses the zeroth derivative rather than Taylor.
All constants are uniform over the shifts defining the affine loci. -/
theorem weighted_inv_separation_mul_norm_le
    {𝕜 : Type*} [NormedField 𝕜]
    {ι E F : Type u} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap (ι → E) F) (N k L : ℕ) (hk : k ≤ L) (hN : N ≤ L)
    (pairs : Finset (ι × ι)) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (shift : ι → ι → E)
    (hflat : ∀ j < N, ∀ a : ι → E, ∀ p ∈ pairs,
      a p.1 = a p.2 + shift p.1 p.2 → iteratedFDeriv ℝ j f a = 0)
    (X : ι → E) (hX : ∀ p ∈ pairs, X p.1 ≠ X p.2 + shift p.1 p.2) :
    (1 + ‖X‖) ^ k * ((affineCoincidenceSeparation pairs shift X ^ N)⁻¹ * ‖f X‖) ≤
      2 ^ (k + L) * (Finset.Iic (L, L)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f := by
  let δ := affineCoincidenceSeparation pairs shift X
  have hδpos : 0 < δ := affineCoincidenceSeparation_pos pairs shift X hX
  have hδle : δ ≤ 1 := affineCoincidenceSeparation_le_one pairs shift X
  rcases eq_or_lt_of_le hδle with hδ | hδ
  · have hbase := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := 𝕜) (m := (L, L)) hk (Nat.zero_le L) f X
    change (1 + ‖X‖) ^ k * ((δ ^ N)⁻¹ * ‖f X‖) ≤ _
    rw [hδ, one_pow, inv_one, one_mul]
    simp only [norm_iteratedFDeriv_zero] at hbase
    apply hbase.trans
    apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · obtain ⟨p, a, hp, ha, hdist⟩ :=
      exists_affine_coincidence_at_separation pairs hne shift X hδ
    have hb := weighted_norm_le_pow_mul_sup_seminorm_of_flat
      (𝕜 := 𝕜) f N k L hk hN
      (a := a) (x := X) (hdist.trans_le hδle)
      (fun j hj => hflat j hj a p hp ha)
    rw [hdist] at hb
    have hinv : 0 ≤ (δ ^ N)⁻¹ := by positivity
    have hpow : δ ^ N ≠ 0 := ne_of_gt (pow_pos hδpos N)
    calc
      _ = (δ ^ N)⁻¹ * ((1 + ‖X‖) ^ k * ‖f X‖) := by ring
      _ ≤ (δ ^ N)⁻¹ * (δ ^ N * (2 ^ (k + L) *
          (Finset.Iic (L, L)).sup
            (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f)) :=
        mul_le_mul_of_nonneg_left hb hinv
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]

/-- An unweighted version ready for an integrable Schwartz majorant. -/
theorem inv_separation_mul_norm_le
    {𝕜 : Type*} [NormedField 𝕜]
    {ι E F : Type u} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap (ι → E) F) (N k L : ℕ) (hk : k ≤ L) (hN : N ≤ L)
    (pairs : Finset (ι × ι)) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (shift : ι → ι → E)
    (hflat : ∀ j < N, ∀ a : ι → E, ∀ p ∈ pairs,
      a p.1 = a p.2 + shift p.1 p.2 → iteratedFDeriv ℝ j f a = 0)
    (X : ι → E) (hX : ∀ p ∈ pairs, X p.1 ≠ X p.2 + shift p.1 p.2) :
    (affineCoincidenceSeparation pairs shift X ^ N)⁻¹ * ‖f X‖ ≤
      (2 ^ (k + L) * (Finset.Iic (L, L)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f) *
      ((1 + ‖X‖) ^ k)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖X‖) ^ k)).mpr
  simpa only [mul_comm] using
    weighted_inv_separation_mul_norm_le f N k L hk hN pairs hne shift hflat X hX

@[simp] theorem affineCoincidenceSeparation_empty
    {ι E : Type*} [NormedAddCommGroup E] (shift : ι → ι → E) (X : ι → E) :
    affineCoincidenceSeparation ∅ shift X = 1 := by
  classical
  simp [affineCoincidenceSeparation]

/-- Joint maximum-norm decay is bounded by the product of one-point center
weights, without any dimension-dependent integration constant. -/
theorem joint_centerWeight_le_prod
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (q : ℕ) (X : ι → E) :
    EuclideanField.centerWeight (q * Fintype.card ι) X ≤
      ∏ i, EuclideanField.centerWeight q (X i) := by
  have hp : 0 < ∏ i, (1 + ‖X i‖) ^ q :=
    Finset.prod_pos fun i _ => by positivity
  have hprod : (∏ i, (1 + ‖X i‖) ^ q) ≤ (1 + ‖X‖) ^ (q * Fintype.card ι) := by
    calc
      _ ≤ ∏ _ : ι, (1 + ‖X‖) ^ q := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro i _
        exact pow_le_pow_left₀ (by positivity)
          (by linarith [norm_le_pi_norm X i]) q
      _ = _ := by simp [← pow_mul]
  simpa only [EuclideanField.centerWeight, Finset.prod_inv_distrib] using
    inv_anti₀ hp hprod

/-- A singular scalar kernel against a joint flat test has a product majorant.
The statement includes every configuration, including coincidences. No bound on
an arbitrary diagonal totalization of the scalar kernel is required. -/
theorem norm_smul_le_prod_centerWeight_of_affine_flat
    {𝕜 : Type*} [NormedField 𝕜]
    {ι E F : Type u} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap (ι → E) F) (N q L : ℕ)
    (hNpos : 0 < N) (hq : q * Fintype.card ι ≤ L) (hN : N ≤ L)
    (pairs : Finset (ι × ι)) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (shift : ι → ι → E)
    (hflat : ∀ j < N, ∀ a : ι → E, ∀ p ∈ pairs,
      a p.1 = a p.2 + shift p.1 p.2 → iteratedFDeriv ℝ j f a = 0)
    (K : (ι → E) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ X, (∀ p ∈ pairs, X p.1 ≠ X p.2 + shift p.1 p.2) →
      ‖K X‖ ≤ A * (affineCoincidenceSeparation pairs shift X ^ N)⁻¹)
    (X : ι → E) :
    ‖K X • f X‖ ≤
      (A * 2 ^ (q * Fintype.card ι + L) * (Finset.Iic (L, L)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f) *
        ∏ i, EuclideanField.centerWeight q (X i) := by
  classical
  by_cases hX : ∀ p ∈ pairs, X p.1 ≠ X p.2 + shift p.1 p.2
  · have hf := inv_separation_mul_norm_le (𝕜 := 𝕜) f N (q * Fintype.card ι) L
      hq hN pairs hne shift hflat X hX
    calc
      _ = ‖K X‖ * ‖f X‖ := norm_smul _ _
      _ ≤ (A * (affineCoincidenceSeparation pairs shift X ^ N)⁻¹) * ‖f X‖ :=
        mul_le_mul_of_nonneg_right (hK X hX) (norm_nonneg _)
      _ = A * ((affineCoincidenceSeparation pairs shift X ^ N)⁻¹ * ‖f X‖) := by ring
      _ ≤ A * ((2 ^ (q * Fintype.card ι + L) * (Finset.Iic (L, L)).sup
          (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f) *
            EuclideanField.centerWeight (q * Fintype.card ι) X) :=
        mul_le_mul_of_nonneg_left hf hA
      _ ≤ A * ((2 ^ (q * Fintype.card ι + L) * (Finset.Iic (L, L)).sup
          (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f) *
            ∏ i, EuclideanField.centerWeight q (X i)) := by
        gcongr
        exact joint_centerWeight_le_prod q X
      _ = _ := by ring
  · push Not at hX
    obtain ⟨p, hp, he⟩ := hX
    have hfx : f X = 0 := by
      apply norm_eq_zero.mp
      have hz := congrArg norm (hflat 0 hNpos X p hp he)
      simpa only [norm_iteratedFDeriv_zero, norm_zero] using hz
    rw [hfx, smul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hA (by positivity)) (apply_nonneg _ _))
      (Finset.prod_nonneg fun i _ => EuclideanField.centerWeight_nonneg q (X i))

/-- Absolute integrability and the quantitative integrated estimate follow from
one-point center-weight integrability and finite-product Fubini. -/
theorem integrable_smul_and_norm_integral_le_of_affine_flat
    {𝕜 : Type*} [NormedField 𝕜]
    {ι E F : Type u} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
    [SigmaFinite (volume : Measure E)]
    (f : SchwartzMap (ι → E) F) (N q L : ℕ)
    (hNpos : 0 < N) (hq : q * Fintype.card ι ≤ L) (hN : N ≤ L)
    (hqint : Module.finrank ℝ E < q)
    (pairs : Finset (ι × ι)) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (shift : ι → ι → E)
    (hflat : ∀ j < N, ∀ a : ι → E, ∀ p ∈ pairs,
      a p.1 = a p.2 + shift p.1 p.2 → iteratedFDeriv ℝ j f a = 0)
    (K : (ι → E) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ X, (∀ p ∈ pairs, X p.1 ≠ X p.2 + shift p.1 p.2) →
      ‖K X‖ ≤ A * (affineCoincidenceSeparation pairs shift X ^ N)⁻¹)
    (hmeas : AEStronglyMeasurable (fun X => K X • f X)
      (Measure.pi fun _ : ι => (volume : Measure E))) :
    Integrable (fun X => K X • f X) (Measure.pi fun _ : ι => (volume : Measure E)) ∧
      ‖∫ X, K X • f X ∂(Measure.pi fun _ : ι => (volume : Measure E))‖ ≤
        (A * 2 ^ (q * Fintype.card ι + L) * (Finset.Iic (L, L)).sup
          (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f) *
          (∫ x : E, EuclideanField.centerWeight q x) ^ Fintype.card ι := by
  let B := A * 2 ^ (q * Fintype.card ι + L) * (Finset.Iic (L, L)).sup
    (fun p : ℕ × ℕ => SchwartzMap.seminorm 𝕜 p.1 p.2) f
  have hW := EuclideanField.integrable_centerWeight (E := E) q hqint
  have hmajor := (Integrable.fintype_prod (fun _ : ι => hW)).const_mul B
  have hbound : ∀ X : ι → E, ‖K X • f X‖ ≤
      B * ∏ i, EuclideanField.centerWeight q (X i) :=
    norm_smul_le_prod_centerWeight_of_affine_flat (𝕜 := 𝕜)
      f N q L hNpos hq hN pairs hne shift hflat K hA hK
  refine ⟨hmajor.mono' hmeas (Filter.Eventually.of_forall hbound), ?_⟩
  have hb := norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hbound)
  simpa only [integral_const_mul, integral_fintype_prod_eq_prod,
    Finset.prod_const, Finset.card_univ] using hb

end YangMills.Analysis
