import MixingCoefficientTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.MixingTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre
open YMYMG.DictionaryRenormalization YMYMG.CouplingTaylor
open YMYMG.LegendreTransport YMYMG.ScaleTransport
variable {G : CompactSimpleGaugeGroup}

def pairedConvolve {U V : Type*} (B : U → V → ℂ)
    (c : ℕ → ℕ → U) (w : ℕ → ℕ → V) (r l : ℕ) : ℂ :=
  ∑ i : Fin (r+1), ∑ j : Fin (l+1), B (c i.val j.val) (w (r-i.val) (l-j.val))

theorem pairedConvolve_swap {U V : Type*} (B : U → V → ℂ)
    (c : ℕ → ℕ → U) (w : ℕ → ℕ → V) (r l : ℕ) :
    pairedConvolve B c w r l = pairedConvolve (fun v u => B u v) w c r l := by
  unfold pairedConvolve
  apply Fintype.sum_equiv Fin.revPerm
  intro i
  apply Fintype.sum_equiv Fin.revPerm
  intro j
  have hi := i.add_rev_cast
  have hj := j.add_rev_cast
  have hi' : r - i.rev.val = i.val := by omega
  have hj' : l - j.rev.val = j.val := by omega
  have hi'' : i.rev.val = r - i.val := by omega
  have hj'' : j.rev.val = l - j.val := by omega
  simp only [Fin.revPerm_apply]
  rw [hi', hj', hi'', hj'']

theorem pairedConvolve_delay_left {U V : Type*} [Zero U]
    (B : U → V → ℂ) (hB : ∀ v, B 0 v = 0)
    (c : ℕ → ℕ → U) (w : ℕ → ℕ → V) (r l : ℕ) :
    pairedConvolve B (delay c) w r l = delay (pairedConvolve B c w) r l := by
  cases l with
  | zero => simp [pairedConvolve, delay, hB]
  | succ l =>
    cases r with
    | zero => simp [pairedConvolve, delay, hB]
    | succ r =>
      cases r with
      | zero => simp [pairedConvolve, delay, Fin.sum_univ_succ, hB]
      | succ r =>
        change pairedConvolve B (delay c) w (r+2) (l+1) = pairedConvolve B c w r l
        unfold pairedConvolve
        conv_lhs => rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, delay, hB, Finset.sum_const_zero, zero_add, Fin.val_succ]
        conv_lhs => rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, hB, Finset.sum_const_zero, zero_add,
          Fin.val_succ, Nat.add_sub_add_right]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, hB, zero_add, Fin.val_succ, Nat.add_sub_add_right]

theorem pairedConvolve_delay_right {U V : Type*} [Zero V]
    (B : U → V → ℂ) (hB : ∀ u, B u 0 = 0)
    (c : ℕ → ℕ → U) (w : ℕ → ℕ → V) (r l : ℕ) :
    pairedConvolve B c (delay w) r l = delay (pairedConvolve B c w) r l := by
  rw [pairedConvolve_swap, pairedConvolve_delay_left _ hB]
  exact congrArg (fun f : ℕ → ℕ → ℂ => delay f r l)
    (by funext i j; exact pairedConvolve_swap _ w c i j)

def evaluate (J : InvariantInsertionLabel G → ℂ) : (InvariantInsertionLabel G →₀ ℝ) →ₗ[ℝ] ℂ :=
  Finsupp.linearCombination ℝ J

theorem evaluate_apply (J : InvariantInsertionLabel G → ℂ)
    (c : InvariantInsertionLabel G →₀ ℝ) :
    evaluate J c = c.sum (fun p a => (a : ℂ)*J p) := by
  simp only [evaluate, Finsupp.linearCombination_apply, Complex.real_smul]

theorem mixingAction_paired (K : CompositeMixing G) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G)
    (r l : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    mixingAction K mu J p r l legs q =
      pairedConvolve (fun c w => evaluate w c) (fun i j => K.coefficient mu i j p)
        (fun i j label => J label i j legs q) r l := by
  simp only [mixingAction, pairedConvolve, evaluate_apply]

theorem mixingAction_add (K H : CompositeMixing G) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (addMixing K H) mu J p =
      mixingAction K mu J p + mixingAction H mu J p := by
  funext r l legs q
  simp only [mixingAction_paired, pairedConvolve, addMixing, map_add,
    Pi.add_apply, Finset.sum_add_distrib]

theorem mixingAction_scale (K : CompositeMixing G) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (scaleMixing K a ha) mu J p = (a mu : ℂ) • mixingAction K mu J p := by
  funext r l legs q
  simp only [mixingAction_paired, pairedConvolve, scaleMixing, map_smul,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, Finset.mul_sum]

theorem mixingAction_sub (K H : CompositeMixing G) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (subMixing K H) mu J p =
      mixingAction K mu J p - mixingAction H mu J p := by
  rw [subMixing, mixingAction_add, mixingAction_scale]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, sub_eq_add_neg]

theorem mixingAction_input (K : CompositeMixing G) (D : Direction G) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (inputMixing K D) mu J p =
      (D.weight p : ℂ) • mixingAction K mu J D.lower := by
  funext r l legs q
  simp only [mixingAction_paired, pairedConvolve, inputMixing, map_smul,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, Finset.mul_sum]

theorem mixingAction_delay (K : CompositeMixing G) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (delayMixing K) mu J p = amplitudeDelay (mixingAction K mu J p) := by
  funext r l legs q
  simp only [mixingAction_paired, delayMixing, amplitudeDelay]
  exact pairedConvolve_delay_left _ (fun _ => map_zero _) _ _ r l

theorem mixingAction_dictionary_delay (K : CompositeMixing G) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction K mu (fun label => amplitudeDelay (J label)) p =
      amplitudeDelay (mixingAction K mu J p) := by
  funext r l legs q
  have hh : (fun i j label => amplitudeDelay (J label) i j legs q) =
      delay (fun i j label => J label i j legs q) := by
    funext i j label
    obtain i | i | i := i <;> cases j <;> rfl
  simp only [mixingAction_paired, amplitudeDelay]
  rw [show (fun i j label => delay (fun a b => J label a b legs q) i j) =
      delay (fun i j label => J label i j legs q) from hh]
  apply pairedConvolve_delay_right
  intro c
  simp only [evaluate, Finsupp.linearCombination_zero, LinearMap.zero_apply]

def dictionaryChange (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (D : Direction G) (a : ℝ) : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G :=
  J + D.weight.smulRight (a • amplitudeDelay (J D.lower))

theorem dictionaryChange_apply (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (D : Direction G) (a : ℝ) (p : InvariantInsertionLabel G) :
    dictionaryChange J D a p = J p + (a * D.weight p : ℝ) • amplitudeDelay (J D.lower) := by
  simp only [dictionaryChange, LinearMap.add_apply, LinearMap.smulRight_apply, smul_smul]
  rw [mul_comm]

theorem dictionaryChange_lower (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (D : Direction G) (hq : D.weight D.lower = 0) (a : ℝ) :
    dictionaryChange J D a D.lower = J D.lower := by
  simp only [dictionaryChange_apply, hq, mul_zero, zero_smul, add_zero]

def sliceLinear (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (r l : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    InvariantInsertionLabel G →ₗ[ℝ] ℂ where
  toFun p := J p r l legs q
  map_add' p t := by simp only [map_add, Pi.add_apply]
  map_smul' c p := by simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem differenceMixing_action_congr (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0) (mu : ℝ)
    (J H : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (hJH : J D.lower = H D.lower) (p : InvariantInsertionLabel G) :
    mixingAction (differenceMixing K D hq) mu J p =
      mixingAction (differenceMixing K D hq) mu H p := by
  funext r l legs q
  simp only [mixingAction_paired, pairedConvolve, differenceMixing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change Finsupp.linearCombination ℝ (sliceLinear J _ _ legs q)
      (outputDifference D hq _) =
    Finsupp.linearCombination ℝ (sliceLinear H _ _ legs q) (outputDifference D hq _)
  rw [outputDifference_evaluate, outputDifference_evaluate]
  simp only [sliceLinear, LinearMap.coe_mk, AddHom.coe_mk, hJH]

def sliceDelayLinear (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (r l : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    InvariantInsertionLabel G →ₗ[ℝ] ℂ where
  toFun p := amplitudeDelay (J p) r l legs q
  map_add' p t := by
    rw [map_add, amplitudeDelay_add]
    rfl
  map_smul' c p := by
    rw [map_smul]
    obtain r | r | r := r <;> cases l
    all_goals simp [amplitudeDelay, delay]

theorem evaluate_dictionaryChange (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G)
    (D : Direction G) (hq : D.weight D.lower = 0) (a : ℝ)
    (c : InvariantInsertionLabel G →₀ ℝ)
    (r l : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    evaluate (fun p => dictionaryChange J D a p r l legs q) c =
      evaluate (fun p => J p r l legs q) c +
      (a : ℂ) * evaluate (fun p => amplitudeDelay (J p) r l legs q) (outputDifference D hq c) := by
  change evaluate _ c = evaluate _ c + (a : ℂ) *
    Finsupp.linearCombination ℝ (sliceDelayLinear J r l legs q) (outputDifference D hq c)
  rw [outputDifference_evaluate]
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, hc, hd, add_smul, mul_add]
    ring
  | single p b =>
    simp only [evaluate, Finsupp.linearCombination_single, dictionaryChange_apply,
      Pi.add_apply, Pi.smul_apply, sliceDelayLinear, LinearMap.coe_mk,
      AddHom.coe_mk, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
    ring

theorem mixingAction_dictionaryChange (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0) (mu a : ℝ)
    (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction K mu (dictionaryChange J D a) p = mixingAction K mu J p +
      (a : ℂ) • amplitudeDelay (mixingAction (differenceMixing K D hq) mu J p) := by
  rw [← mixingAction_dictionary_delay]
  funext r l legs q
  simp only [mixingAction_paired, pairedConvolve, evaluate_dictionaryChange J D hq,
    differenceMixing, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem rankMixing_action (D : Direction G) (f : ℝ → ℕ → ℕ → ℝ)
    (hf : ∀ r l, ContDiffOn ℝ ∞ (fun mu => f mu r l) (Set.Ioi 0))
    (hf0 : ∀ mu r, 0 < mu → f mu r 0 = 0) (mu : ℝ)
    (J : InvariantInsertionLabel G → FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (rankMixing D f hf hf0) mu J p =
      (D.weight p : ℂ) • scalarAction (f mu) (J D.lower) := by
  funext r l legs q
  simp only [mixingAction_paired, pairedConvolve, rankMixing, evaluate,
    Finsupp.linearCombination_single, Complex.real_smul, Complex.ofReal_mul,
    scalarAction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem amplitudeDelay_smul (c : ℂ) (A : FormalAmplitude G) :
    amplitudeDelay (c • A) = c • amplitudeDelay A := by
  funext r l legs q
  obtain r | r | r := r <;> cases l <;> simp [amplitudeDelay, delay]

/-- The native mixing action transforms in the column-label convention.
The remaining scalarAction is exactly the rate used to cancel both
product-rule terms; its expansion is treated separately. -/
theorem changeMixing_action (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0) (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (mu : ℝ)
    (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (changeMixing K D hq beta a ha) mu (dictionaryChange J D (a mu)) p =
      mixingAction K mu J p +
      (a mu * D.weight p : ℝ) • amplitudeDelay (mixingAction K mu J D.lower) -
      (D.weight p : ℂ) • scalarAction (correctionRate beta a mu) (J D.lower) := by
  unfold changeMixing
  simp only [mixingAction_sub, mixingAction_add, mixingAction_scale,
    mixingAction_delay, mixingAction_input, rateMixing, rankMixing_action,
    dictionaryChange_lower J D hq]
  rw [differenceMixing_action_congr K D hq mu _ J (dictionaryChange_lower J D hq (a mu)),
    differenceMixing_action_congr (inputMixing K D) D hq mu _ J
      (dictionaryChange_lower J D hq (a mu))]
  have hi : differenceMixing (inputMixing K D) D hq = inputMixing (differenceMixing K D hq) D := by
    unfold differenceMixing inputMixing
    congr 1
    funext mu r l label
    exact map_smul (outputDifference D hq) _ _
  rw [hi, mixingAction_input, mixingAction_dictionaryChange K D hq,
    mixingAction_dictionaryChange K D hq]
  simp only [amplitudeDelay_add, amplitudeDelay_smul]
  funext r l legs q
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_mul]
  ring

#print axioms pairedConvolve_swap
#print axioms pairedConvolve_delay_left
#print axioms pairedConvolve_delay_right
#print axioms evaluate_apply
#print axioms mixingAction_paired
#print axioms mixingAction_add
#print axioms mixingAction_scale
#print axioms mixingAction_sub
#print axioms mixingAction_input
#print axioms mixingAction_delay
#print axioms mixingAction_dictionary_delay
#print axioms dictionaryChange_apply
#print axioms dictionaryChange_lower
#print axioms differenceMixing_action_congr
#print axioms evaluate_dictionaryChange
#print axioms mixingAction_dictionaryChange
#print axioms rankMixing_action
#print axioms amplitudeDelay_smul
#print axioms changeMixing_action
end YMYMG.MixingTransport
