import YangMills.Analysis.SchwartzSeminorms
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section
open MeasureTheory
open scoped SchwartzMap BigOperators

namespace EuclideanField

variable {E : Type*} [NormedAddCommGroup E]

/-- Independent relative and center coordinates for a collection of pairs.
The second endpoint of each pair is the center itself. -/
def pairCoordinates {r : ℕ} (u y : Fin r → E) : Fin (r + r) → E :=
  Fin.addCases (fun i => u i + y i) y

@[simp] lemma pairCoordinates_left {r : ℕ} (u y : Fin r → E) (i : Fin r) :
    pairCoordinates u y (Fin.castAdd r i) = u i + y i := by
  simp only [pairCoordinates, Fin.addCases_left]

@[simp] lemma pairCoordinates_right {r : ℕ} (u y : Fin r → E) (i : Fin r) :
    pairCoordinates u y (Fin.natAdd r i) = y i := by
  simp only [pairCoordinates, Fin.addCases_right]

lemma norm_center_le_pairCoordinates {r : ℕ} (u y : Fin r → E) (i : Fin r) :
    ‖y i‖ ≤ ‖pairCoordinates u y‖ := by
  simpa only [pairCoordinates_right] using norm_le_pi_norm (pairCoordinates u y) (Fin.natAdd r i)

lemma continuous_pairCoordinates (r : ℕ) :
    Continuous (fun p : (Fin r → E) × (Fin r → E) => pairCoordinates p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [pairCoordinates_left]
    fun_prop
  · intro j
    simp only [pairCoordinates_right]
    fun_prop

/-- Integrable polynomial center weight. -/
def centerWeight (q : ℕ) (y : E) : ℝ := ((1 + ‖y‖) ^ q)⁻¹

lemma centerWeight_nonneg (q : ℕ) (y : E) : 0 ≤ centerWeight q y := by
  unfold centerWeight
  positivity

lemma centerWeight_pos (q : ℕ) (y : E) : 0 < centerWeight q y := by
  unfold centerWeight
  positivity

lemma pair_center_weight_bound {r q L : ℕ} (hL : q * r ≤ L)
    (u y : Fin r → E) :
    (∏ i, (1 + ‖y i‖) ^ q) ≤ (1 + ‖pairCoordinates u y‖) ^ L := by
  calc (∏ i, (1 + ‖y i‖) ^ q)
      ≤ ∏ _ : Fin r, (1 + ‖pairCoordinates u y‖) ^ q := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _
          exact pow_le_pow_left₀ (by positivity)
            (by linarith [norm_center_le_pairCoordinates u y i]) q
    _ = (1 + ‖pairCoordinates u y‖) ^ (q * r) := by
      simp [← pow_mul]
    _ ≤ (1 + ‖pairCoordinates u y‖) ^ L :=
      pow_le_pow_right₀ (by linarith [norm_nonneg (pairCoordinates u y)]) hL

/-- Global Schwartz decay controls each center independently with one common
weight order proportional to the number of pairs. -/
lemma norm_le_pair_center_weight {r q L : ℕ} (hL : q * r ≤ L)
    (F : (Fin (r + r) → E) → ℂ) {B : ℝ}
    (hF : ∀ x, (1 + ‖x‖) ^ L * ‖F x‖ ≤ B) (u y : Fin r → E) :
    ‖F (pairCoordinates u y)‖ ≤ B * ∏ i, centerWeight q (y i) := by
  have hp : 0 < ∏ i, (1 + ‖y i‖) ^ q :=
    Finset.prod_pos fun i _ => pow_pos (by positivity) _
  have hprod : (∏ i, (1 + ‖y i‖) ^ q) * ‖F (pairCoordinates u y)‖ ≤ B :=
    (mul_le_mul_of_nonneg_right (pair_center_weight_bound hL u y) (norm_nonneg _)).trans (hF _)
  simpa only [centerWeight, Finset.prod_inv_distrib, div_eq_mul_inv] using
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hprod)


variable [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E] [SigmaFinite (volume : Measure E)]

omit [SecondCountableTopology E] [SigmaFinite (volume : Measure E)] in
lemma integrable_centerWeight [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (q : ℕ) (hq : Module.finrank ℝ E < q) :
    Integrable (centerWeight q : E → ℝ) := by
  have heq : (centerWeight q : E → ℝ) = fun x : E => (1 + ‖x‖) ^ (-(q : ℝ)) := by
    funext x
    simp [centerWeight]
  rw [heq]
  exact (integrable_one_add_norm (E := E) (μ := volume) (by exact_mod_cast hq :
      (Module.finrank ℝ E : ℝ) < (q : ℝ)))

/-- A product of scalar relative kernels applied to a joint test. Coordinates
are relative variables followed by centers, all with ordinary product volume. -/
def pairKernelIntegrand {r : ℕ} (G : E → ℝ)
    (F : (Fin (r + r) → E) → ℂ) (p : (Fin r → E) × (Fin r → E)) : ℂ :=
  ((∏ i, G (p.1 i) : ℝ) : ℂ) * F (pairCoordinates p.1 p.2)

omit [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [SigmaFinite (volume : Measure E)] in
private lemma pairKernel_domination {r q L : ℕ} (hL : q * r ≤ L)
    (G : E → ℝ) (F : (Fin (r + r) → E) → ℂ) {B : ℝ}
    (hF : ∀ x, (1 + ‖x‖) ^ L * ‖F x‖ ≤ B)
    (p : (Fin r → E) × (Fin r → E)) :
    ‖pairKernelIntegrand G F p‖ ≤
      B * ((∏ i, ‖G (p.1 i)‖) * ∏ i, centerWeight q (p.2 i)) := by
  simp only [pairKernelIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Finset.abs_prod]
  calc (∏ i, |G (p.1 i)|) * ‖F (pairCoordinates p.1 p.2)‖
      ≤ (∏ i, |G (p.1 i)|) * (B * ∏ i, centerWeight q (p.2 i)) :=
        mul_le_mul_of_nonneg_left (norm_le_pair_center_weight hL F hF p.1 p.2)
          (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = _ := by ring

/-- The paired scalar kernel is integrable even though the scalar kernel on
all absolute variables is not integrable: Schwartz decay controls centers. -/
lemma integrable_pair_kernel {r q L : ℕ} (hL : q * r ≤ L)
    {G : E → ℝ} (hG : Integrable G) (hW : Integrable (centerWeight q : E → ℝ))
    {F : (Fin (r + r) → E) → ℂ} (hFc : Continuous F) {B : ℝ}
    (hF : ∀ x, (1 + ‖x‖) ^ L * ‖F x‖ ≤ B) :
    Integrable (pairKernelIntegrand G F)
      ((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
        (Measure.pi fun _ : Fin r => (volume : Measure E))) := by
  have hGp := Integrable.fintype_prod (fun _ : Fin r => hG.norm)
  have hWp := Integrable.fintype_prod (fun _ : Fin r => hW)
  apply ((hGp.mul_prod hWp).const_mul B).mono'
  · have hg := (Integrable.fintype_prod (fun _ : Fin r => hG)).ofReal (𝕜 := ℂ)
    exact hg.aestronglyMeasurable.comp_fst.mul
      (hFc.comp (continuous_pairCoordinates r)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (pairKernel_domination hL G F hF)

omit [BorelSpace E] [SecondCountableTopology E] in
/-- Uniform paired-kernel bound: only one L¹ factor for each relative
variable and one fixed polynomial-weight factor for each center. -/
lemma norm_integral_pair_kernel_le {r q L : ℕ} (hL : q * r ≤ L)
    {G : E → ℝ} (hG : Integrable G) (hW : Integrable (centerWeight q : E → ℝ))
    {F : (Fin (r + r) → E) → ℂ} {B : ℝ}
    (hF : ∀ x, (1 + ‖x‖) ^ L * ‖F x‖ ≤ B) :
    ‖∫ p, pairKernelIntegrand G F p
      ∂((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
        (Measure.pi fun _ : Fin r => (volume : Measure E)))‖ ≤
      B * ((∫ x, ‖G x‖) * (∫ y : E, centerWeight q y)) ^ r := by
  have hGp := Integrable.fintype_prod (fun _ : Fin r => hG.norm)
  have hWp := Integrable.fintype_prod (fun _ : Fin r => hW)
  have hb := norm_integral_le_of_norm_le ((hGp.mul_prod hWp).const_mul B)
    (Filter.Eventually.of_forall (pairKernel_domination hL G F hF))
  convert hb using 1
  rw [integral_const_mul, integral_prod_mul
    (fun u : Fin r → E => ∏ i, ‖G (u i)‖)
    (fun y : Fin r → E => ∏ i, centerWeight q (y i))]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin r => fun x : E => ‖G x‖),
    integral_fintype_prod_eq_prod (fun _ : Fin r => centerWeight (E := E) q)]
  simp only [Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_pow]


/-- The center/difference change of variables preserves product volume
exactly; in Euclidean coordinates its Jacobian is one. -/
lemma pairCoordinates_measurePreserving [(volume : Measure E).IsAddRightInvariant] (r : ℕ) :
    MeasurePreserving (fun p : (Fin r → E) × (Fin r → E) => pairCoordinates p.1 p.2)
      ((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
        (Measure.pi fun _ : Fin r => (volume : Measure E)))
      (Measure.pi fun _ : Fin (r + r) => (volume : Measure E)) := by
  have hs := measurePreserving_add_prod
    (μ := Measure.pi fun _ : Fin r => (volume : Measure E))
    (ν := Measure.pi fun _ : Fin r => (volume : Measure E))
  have ha := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin r ⊕ Fin r => (volume : Measure E))
  have hr := measurePreserving_piCongrLeft
    (fun _ : Fin (r + r) => (volume : Measure E)) (finSumFinEquiv : Fin r ⊕ Fin r ≃ _)
  convert hr.comp (ha.comp hs) using 1
  funext p i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [pairCoordinates, Function.comp_def, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  · intro j
    simp only [pairCoordinates_right, Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply, finSumFinEquiv_symm_apply_natAdd,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    simp


variable [NormedSpace ℝ E]

omit [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [SigmaFinite (volume : Measure E)] in
/-- Applying unit directional derivatives keeps the same weighted derivative
bound; in particular coordinate partial derivatives have no extra constant. -/
lemma weighted_iteratedLineDeriv_bound {N k L : ℕ}
    (h : 𝓢(Fin N → E, ℂ)) (v : Fin k → (Fin N → E))
    (hv : ∀ i, ‖v i‖ ≤ 1) {B : ℝ}
    (hB : ∀ x, (1 + ‖x‖) ^ L * ‖iteratedFDeriv ℝ k h x‖ ≤ B) (x : Fin N → E) :
    (1 + ‖x‖) ^ L *
      ‖LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin N → E, ℂ) v h x‖ ≤ B := by
  rw [LineDeriv.iteratedLineDerivOpCLM_apply, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  apply le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (hB x)
  apply ContinuousMultilinearMap.unit_le_opNorm
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hv

/-- L¹ control of a paired differentiated Schwartz kernel, with every
derivative remaining on the test function. -/
lemma integrable_differentiated_pair_kernel {r q L k : ℕ} (hL : q * r ≤ L)
    {G : E → ℝ} (hG : Integrable G) (hW : Integrable (centerWeight q : E → ℝ))
    (h : 𝓢(Fin (r + r) → E, ℂ)) (v : Fin k → (Fin (r + r) → E))
    (hv : ∀ i, ‖v i‖ ≤ 1) {B : ℝ}
    (hB : ∀ x, (1 + ‖x‖) ^ L * ‖iteratedFDeriv ℝ k h x‖ ≤ B) :
    Integrable (pairKernelIntegrand G
      (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin (r + r) → E, ℂ) v h))
      ((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
        (Measure.pi fun _ : Fin r => (volume : Measure E))) :=
  integrable_pair_kernel hL hG hW (SchwartzMap.continuous _)
    (weighted_iteratedLineDeriv_bound h v hv hB)

/-- The uniform bound for any fixed selection of pair derivatives. The
number of derivatives affects only the required test seminorm, not this constant. -/
lemma norm_integral_differentiated_pair_kernel_le {r q L k : ℕ} (hL : q * r ≤ L)
    {G : E → ℝ} (hG : Integrable G) (hW : Integrable (centerWeight q : E → ℝ))
    (h : 𝓢(Fin (r + r) → E, ℂ)) (v : Fin k → (Fin (r + r) → E))
    (hv : ∀ i, ‖v i‖ ≤ 1) {B : ℝ}
    (hB : ∀ x, (1 + ‖x‖) ^ L * ‖iteratedFDeriv ℝ k h x‖ ≤ B) :
    ‖∫ p, pairKernelIntegrand G
      (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin (r + r) → E, ℂ) v h) p
      ∂((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
        (Measure.pi fun _ : Fin r => (volume : Measure E)))‖ ≤
      B * ((∫ x, ‖G x‖) * (∫ y : E, centerWeight q y)) ^ r :=
  norm_integral_pair_kernel_le hL hG hW (weighted_iteratedLineDeriv_bound h v hv hB)


/-- Paired L¹ scalar kernels define a continuous joint Schwartz distribution.
Its proof uses the explicit weighted bound above, not a nuclear-extension estimate. -/
def pairKernelCLM (r q : ℕ) (G : E → ℝ) (hG : Integrable G)
    (hW : Integrable (centerWeight q : E → ℝ)) :
    𝓢(Fin (r + r) → E, ℂ) →L[ℂ] ℂ := by
  let A (h : 𝓢(Fin (r + r) → E, ℂ)) : ℂ :=
    ∫ p, pairKernelIntegrand G h p
      ∂((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
        (Measure.pi fun _ : Fin r => (volume : Measure E)))
  have hweight (h : 𝓢(Fin (r + r) → E, ℂ)) (x : Fin (r + r) → E) :
      (1 + ‖x‖) ^ (q * r) * ‖h x‖ ≤
        2 ^ (q * r) * (Finset.Iic (q * r, 0)).sup
          (schwartzSeminormFamily ℂ (Fin (r + r) → E) ℂ) h := by
    change (1 + ‖x‖) ^ (q * r) * ‖h x‖ ≤
      2 ^ (q * r) * (Finset.Iic (q * r, 0)).sup
        (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h
    simpa using SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (q * r, 0)) (k := q * r) (n := 0) le_rfl le_rfl h x
  have hint (h : 𝓢(Fin (r + r) → E, ℂ)) :=
    integrable_pair_kernel (le_refl (q * r)) hG hW h.continuous (hweight h)
  refine SchwartzMap.mkCLMtoNormedSpace A ?_ ?_ ?_
  · intro f g
    simp only [A, pairKernelIntegrand, add_apply, mul_add]
    exact integral_add (hint f) (hint g)
  · intro c f
    simp only [A, pairKernelIntegrand, smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ c]
    exact integral_const_mul c _
  · refine ⟨Finset.Iic (q * r, 0),
      2 ^ (q * r) * ((∫ x, ‖G x‖) * (∫ y : E, centerWeight q y)) ^ r, ?_, ?_⟩
    · have hw0 : 0 ≤ ∫ y : E, centerWeight q y := integral_nonneg (centerWeight_nonneg q)
      positivity
    · intro h
      have hb := norm_integral_pair_kernel_le (le_refl (q * r)) hG hW (hweight h)
      simpa only [A, mul_assoc, mul_left_comm, mul_comm] using hb

@[simp] lemma pairKernelCLM_apply (r q : ℕ) (G : E → ℝ) (hG : Integrable G)
    (hW : Integrable (centerWeight q : E → ℝ)) (h : 𝓢(Fin (r + r) → E, ℂ)) :
    pairKernelCLM r q G hG hW h =
      ∫ p, pairKernelIntegrand G h p
        ∂((Measure.pi fun _ : Fin r => (volume : Measure E)).prod
          (Measure.pi fun _ : Fin r => (volume : Measure E))) := rfl


/-- A paired scalar kernel on an elementary product factors into its genuine
two-slot covariance integrals. This includes the empty product. -/
lemma pairKernelCLM_product (r q : ℕ) (G : E → ℝ) (hG : Integrable G)
    (hW : Integrable (centerWeight q : E → ℝ)) (f : Fin (r + r) → 𝓢(E, ℂ)) :
    pairKernelCLM r q G hG hW (GaussianField.complexProductTensor f) =
      ∏ i : Fin r, ∫ p : E × E, (G p.1 : ℂ) *
        f (Fin.castAdd r i) (p.1 + p.2) * f (Fin.natAdd r i) p.2
          ∂((volume : Measure E).prod volume) := by
  rw [pairKernelCLM_apply]
  have hmp := measurePreserving_arrowProdEquivProdArrow E E (Fin r)
    (fun _ => (volume : Measure E)) (fun _ => (volume : Measure E))
  rw [← hmp.integral_comp']
  have heq (p : Fin r → E × E) :
      pairKernelIntegrand G (GaussianField.complexProductTensor f)
        ((MeasurableEquiv.arrowProdEquivProdArrow E E (Fin r)) p) =
        ∏ i : Fin r, (G (p i).1 : ℂ) *
          f (Fin.castAdd r i) ((p i).1 + (p i).2) * f (Fin.natAdd r i) (p i).2 := by
    change ((∏ i, G (p i).1 : ℝ) : ℂ) *
      GaussianField.complexProductTensor f (pairCoordinates (fun i => (p i).1) (fun i => (p i).2)) = _
    simp only [GaussianField.complexProductTensor_apply, Fin.prod_univ_add,
      pairCoordinates_left, pairCoordinates_right, Complex.ofReal_prod,
      Finset.prod_mul_distrib, mul_assoc]
  simp_rw [heq]
  exact integral_fintype_prod_eq_prod (fun i : Fin r => fun p : E × E =>
    (G p.1 : ℂ) * f (Fin.castAdd r i) (p.1 + p.2) * f (Fin.natAdd r i) p.2)

/-- A finite linear combination of paired directional-derivative kernels. -/
def finiteDerivativePairKernelCLM {J : Type*} [Fintype J]
    (r q : ℕ) (G : E → ℝ) (hG : Integrable G)
    (hW : Integrable (centerWeight q : E → ℝ))
    (k : J → ℕ) (v : (j : J) → Fin (k j) → (Fin (r + r) → E))
    (a : J → ℂ) : 𝓢(Fin (r + r) → E, ℂ) →L[ℂ] ℂ :=
  ∑ j, a j • (pairKernelCLM r q G hG hW).comp
    (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin (r + r) → E, ℂ) (v j))

lemma finiteDerivativePairKernelCLM_bound {J : Type*} [Fintype J]
    {r q L : ℕ} (hL : q * r ≤ L) (G : E → ℝ) (hG : Integrable G)
    (hW : Integrable (centerWeight q : E → ℝ))
    (k : J → ℕ) (v : (j : J) → Fin (k j) → (Fin (r + r) → E))
    (hv : ∀ j i, ‖v j i‖ ≤ 1) (a : J → ℂ) (h : 𝓢(Fin (r + r) → E, ℂ))
    {B : ℝ} (hB : ∀ j x, (1 + ‖x‖) ^ L * ‖iteratedFDeriv ℝ (k j) h x‖ ≤ B) :
    ‖finiteDerivativePairKernelCLM r q G hG hW k v a h‖ ≤
      (∑ j, ‖a j‖) * B * ((∫ x, ‖G x‖) * (∫ y : E, centerWeight q y)) ^ r := by
  simp only [finiteDerivativePairKernelCLM, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply]
  calc
    ‖∑ j, a j • pairKernelCLM r q G hG hW
        (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin (r + r) → E, ℂ) (v j) h)‖
      ≤ ∑ j, ‖a j‖ * ‖pairKernelCLM r q G hG hW
        (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin (r + r) → E, ℂ) (v j) h)‖ := by
          simpa only [norm_smul] using norm_sum_le (s := Finset.univ)
            (fun j => a j • pairKernelCLM r q G hG hW
              (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin (r + r) → E, ℂ) (v j) h))
    _ ≤ ∑ j, ‖a j‖ * (B * ((∫ x, ‖G x‖) * (∫ y : E, centerWeight q y)) ^ r) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (norm_integral_differentiated_pair_kernel_le hL hG hW h (v j) (hv j) (hB j))
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring


omit [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [SigmaFinite (volume : Measure E)] in
/-- Differentiating a genuine external product in one slot differentiates
exactly that factor. This is the product agreement needed by mixed pair operators. -/
lemma lineDeriv_single_productTensor {n : ℕ} (f : Fin n → 𝓢(E, ℂ))
    (i : Fin n) (v : E) :
    LineDeriv.lineDerivOpCLM ℂ 𝓢(Fin n → E, ℂ) (Pi.single i v : Fin n → E)
      (GaussianField.complexProductTensor f) =
      GaussianField.complexProductTensor
        (Function.update f i (LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) v (f i))) := by
  ext X
  rw [LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd (j : Fin n) : HasFDerivAt (fun x : Fin n → E => f j (x j))
      ((fderiv ℝ (f j) (X j)).comp (ContinuousLinearMap.proj j)) X :=
    ((f j).hasFDerivAt (X j)).comp X
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => E) j).hasFDerivAt)
  have hp := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd j)
  have hfun : (GaussianField.complexProductTensor f : (Fin n → E) → ℂ) =
      fun x => ∏ j, f j (x j) := by
        funext x
        exact GaussianField.complexProductTensor_apply f x
  rw [hfun, hp.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [GaussianField.complexProductTensor_apply,
      ← Finset.mul_prod_erase Finset.univ (fun j =>
        Function.update f i (LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) v (f i)) j (X j))
        (Finset.mem_univ i)]
    simp only [Pi.single_eq_same, Function.update_self, LineDeriv.lineDerivOpCLM_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

end EuclideanField


namespace EuclideanField

/-- The generic differentiated kernel estimate in the fixed OS seminorm family. -/
lemma finiteDerivativePairKernelCLM_kernelSeminorm_bound {d r q L : ℕ}
    {I J : Type*} [Fintype I] [Fintype J]
    (hL : q * r ≤ L) (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : Integrable G)
    (hW : Integrable (centerWeight q : EuclideanSpace ℝ (Fin d) → ℝ))
    (k : J → ℕ) (hk : ∀ j, k j ≤ L)
    (v : (j : J) → Fin (k j) → (Fin (r + r) → EuclideanSpace ℝ (Fin d)))
    (hv : ∀ j i, ‖v j i‖ ≤ 1) (a : J → ℂ) (h : JointTest d I (r + r))
    (α : Fin (r + r) → I) :
    ‖finiteDerivativePairKernelCLM r q G hG hW k v a (h α)‖ ≤
      (∑ j, ‖a j‖) * kernelSeminorm d I (r + r) L h *
        ((∫ x, ‖G x‖) * (∫ y : EuclideanSpace ℝ (Fin d), centerWeight q y)) ^ r :=
  finiteDerivativePairKernelCLM_bound hL G hG hW k v hv a (h α)
    (fun j x => weighted_iteratedFDeriv_le_kernelSeminorm d I (r + r) L (k j) (hk j) h α x)

end EuclideanField


namespace EuclideanField

/-- Exact ℓ¹ coefficient count when every pair contributes two alternatives. -/
lemma sum_norm_pairChoices {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) :
    (∑ s : ι → Fin 2, ‖∏ i, if s i = 0 then a i else b i‖) =
      ∏ i, (‖a i‖ + ‖b i‖) := by
  simp_rw [norm_prod]
  rw [← Fintype.prod_sum (fun i : ι => fun j : Fin 2 => ‖if j = 0 then a i else b i‖)]
  simp [Fin.sum_univ_two]

/-- The finite derivative-choice coefficients have exponential, rather than
factorial, growth in the number of pairs. -/
lemma sum_norm_pairChoices_le {r : ℕ} (a b : Fin r → ℂ)
    {A B : ℝ} (hA : ∀ i, ‖a i‖ ≤ A) (hB : ∀ i, ‖b i‖ ≤ B) :
    (∑ s : Fin r → Fin 2, ‖∏ i, if s i = 0 then a i else b i‖) ≤ (A + B) ^ r := by
  rw [sum_norm_pairChoices]
  calc (∏ i, (‖a i‖ + ‖b i‖)) ≤ ∏ _ : Fin r, (A + B) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact add_le_add (hA i) (hB i)
    _ = _ := by simp

end EuclideanField


namespace EuclideanField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Distinct slot derivatives differentiate exactly the selected factors. -/
lemma iteratedLineDeriv_distinct_slots_productTensor {n k : ℕ}
    (f : Fin n → SchwartzMap E ℂ) (slot : Fin k ↪ Fin n)
    (v : Fin n → E) :
    LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin n → E, ℂ)
      (fun i => (Pi.single (slot i) (v (slot i)) : Fin n → E))
      (GaussianField.complexProductTensor f) =
    GaussianField.complexProductTensor (fun j =>
      if j ∈ Set.range slot then LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) (v j) (f j) else f j) := by
  classical
  induction k with
  | zero => simp [LineDeriv.iteratedLineDerivOpCLM_apply]
  | succ k ih =>
    let tail : Fin k ↪ Fin n :=
      ⟨fun i => slot i.succ, slot.injective.comp (Fin.succ_injective k)⟩
    change LineDeriv.lineDerivOpCLM ℂ 𝓢(Fin n → E, ℂ)
      (Pi.single (slot 0) (v (slot 0)) : Fin n → E)
      (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(Fin n → E, ℂ)
        (fun i => (Pi.single (tail i) (v (tail i)) : Fin n → E))
        (GaussianField.complexProductTensor f)) = _
    rw [ih tail, lineDeriv_single_productTensor]
    congr 1
    funext j
    by_cases hj : j = slot 0
    · subst j
      have hnot : slot 0 ∉ Set.range tail := by
        rintro ⟨t, ht⟩
        exact Fin.succ_ne_zero t (slot.injective ht)
      simp [hnot, Set.mem_range]
    · have hrange : j ∈ Set.range slot ↔ j ∈ Set.range tail := by
        constructor
        · rintro ⟨a, ha⟩
          obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero (show a ≠ 0 by
            intro ha0; subst a; exact hj ha.symm)
          exact ⟨a, ha⟩
        · rintro ⟨a, ha⟩
          exact ⟨a.succ, ha⟩
      simp only [Function.update_of_ne hj, hrange]

lemma complexProductTensor_piCongrLeft {n N : ℕ} (e : Fin N ≃ Fin n)
    (f : Fin n → SchwartzMap E ℂ) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => E) e)
      (GaussianField.complexProductTensor f) =
    GaussianField.complexProductTensor (fun i => f (e i)) := by
  ext X
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GaussianField.complexProductTensor_apply]
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp [ContinuousLinearEquiv.piCongrLeft, Homeomorph.piCongrLeft, Equiv.piCongrLeft]

end EuclideanField
