import LegendreDictionaryTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! The scale/coupling/field part of the native composite CS equation.
Both product-rule terms of the finite dictionary correction are retained.
This does not choose new mixing or quantum-exact primitive coefficients. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.ScaleTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.Legendre YangMills.ScaleInsertion
open YMYMG.CouplingTaylor YMYMG.WordJet YMYMG.LegendreTransport
open YMYMG.DictionaryRenormalization
variable {G : CompactSimpleGaugeGroup}

def firstDelay (A : FormalAmplitude G) : FormalAmplitude G :=
  fun r l legs q => match r, l with
    | r+1, l+1 => A r l legs q
    | _, _ => 0

theorem amplitudeDelay_add (A H : FormalAmplitude G) :
    amplitudeDelay (A+H) = amplitudeDelay A + amplitudeDelay H := by
  funext r l legs q
  obtain r | r | r := r <;> cases l <;> simp [amplitudeDelay, delay]

theorem amplitudeDelay_sub (A H : FormalAmplitude G) :
    amplitudeDelay (A-H) = amplitudeDelay A - amplitudeDelay H := by
  funext r l legs q
  obtain r | r | r := r <;> cases l <;> simp [amplitudeDelay, delay]

theorem scalarAction_add (beta : ScalarCoefficients) (A H : FormalAmplitude G) :
    scalarAction beta (A+H) = scalarAction beta A + scalarAction beta H := by
  funext r l legs q
  simp only [scalarAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem scalarAction_smul (beta : ScalarCoefficients) (c : ℂ) (A : FormalAmplitude G) :
    scalarAction beta (c • A) = c • scalarAction beta A := by
  funext r l legs q
  simp only [scalarAction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_left_comm]

theorem scalarAction_delay (beta : ScalarCoefficients) (A : FormalAmplitude G) :
    scalarAction beta (amplitudeDelay A) = amplitudeDelay (scalarAction beta A) := by
  funext r l legs q
  exact convolve_delay_right (fun i j => (beta i j : ℂ)) (fun i j => A i j legs q) r l

theorem fieldAction_add (fields : FieldCoefficients) (A H : FormalAmplitude G) :
    fieldAction fields (A+H) = fieldAction fields A + fieldAction fields H := by
  funext r l legs q
  simp only [fieldAction, eulerAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem fieldAction_smul (fields : FieldCoefficients) (c : ℂ) (A : FormalAmplitude G) :
    fieldAction fields (c • A) = c • fieldAction fields A := by
  funext r l legs q
  simp only [fieldAction, eulerAction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_left_comm]

theorem fieldAction_delay (fields : FieldCoefficients) (A : FormalAmplitude G) :
    fieldAction fields (amplitudeDelay A) = amplitudeDelay (fieldAction fields A) := by
  funext r l legs q
  exact convolve_delay_right
    (fun i j => ((legs.map (eulerWeight (fields i j))).sum : ℂ))
    (fun i j => A i j legs q) r l

theorem couplingDerivative_add (A H : FormalAmplitude G) :
    couplingDerivative (A+H) = couplingDerivative A + couplingDerivative H := by
  funext r l legs q
  simp only [couplingDerivative, Pi.add_apply, mul_add]

theorem couplingDerivative_smul (c : ℂ) (A : FormalAmplitude G) :
    couplingDerivative (c • A) = c • couplingDerivative A := by
  funext r l legs q
  simp only [couplingDerivative, Pi.smul_apply, smul_eq_mul, mul_left_comm]

theorem couplingDerivative_delay (A : FormalAmplitude G) :
    couplingDerivative (amplitudeDelay A) =
      amplitudeDelay (couplingDerivative A) + (2 : ℂ) • firstDelay A := by
  funext r l legs q
  obtain r | r | r := r <;> cases l
  all_goals simp [couplingDerivative, amplitudeDelay, firstDelay, delay, smul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  · norm_num
  · ring

def ScaleDifferentiable (J : ℝ → FormalAmplitude G) (mu : ℝ) : Prop :=
  ∀ r l legs q, DifferentiableAt ℝ (fun nu => J nu r l legs q) mu

theorem delay_differentiable (J : ℝ → FormalAmplitude G) (mu : ℝ)
    (hJ : ScaleDifferentiable J mu) :
    ScaleDifferentiable (fun nu => amplitudeDelay (J nu)) mu := by
  intro r l legs q
  obtain r | r | r := r <;> cases l
  all_goals first | exact differentiableAt_const _ | exact hJ _ _ _ _

theorem scaleDerivative_add (J K : ℝ → FormalAmplitude G) (mu : ℝ)
    (hJ : ScaleDifferentiable J mu) (hK : ScaleDifferentiable K mu) :
    scaleDerivative (fun nu => J nu + K nu) mu =
      scaleDerivative J mu + scaleDerivative K mu := by
  funext r l legs q
  simp only [scaleDerivative, Pi.add_apply]
  rw [deriv_fun_add (hJ r l legs q) (hK r l legs q)]
  ring

theorem scaleDerivative_smul_delay (c : ℝ → ℂ) (J : ℝ → FormalAmplitude G) (mu : ℝ)
    (hc : DifferentiableAt ℝ c mu) (hJ : ScaleDifferentiable J mu) :
    scaleDerivative (fun nu => c nu • amplitudeDelay (J nu)) mu =
      c mu • amplitudeDelay (scaleDerivative J mu) +
      ((mu : ℂ) * deriv c mu) • amplitudeDelay (J mu) := by
  funext r l legs q
  obtain r | r | r := r
  · simp [scaleDerivative, amplitudeDelay, delay, smul_eq_mul]
  · simp [scaleDerivative, amplitudeDelay, delay, smul_eq_mul]
  · cases l with
    | zero => simp [scaleDerivative, amplitudeDelay, delay, smul_eq_mul]
    | succ l =>
      simp only [scaleDerivative, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        amplitudeDelay, delay]
      rw [deriv_fun_mul hc (hJ r l legs q)]
      ring

/-- Literally the first three terms of the target's composite residual. -/
def differentialPart (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (J : ℝ → FormalAmplitude G) (mu : ℝ) : FormalAmplitude G :=
  scaleDerivative J mu + scalarAction beta (couplingDerivative (J mu)) - fieldAction fields (J mu)

theorem compositeResidual_parts {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (A : ScaleCouplingFamily G)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (beta : ScalarCoefficients) (fields : FieldCoefficients) (mixing : CompositeMixing G)
    (primitive : (p : InvariantInsertionLabel G) →
      LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (mu : ℝ) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime) :
    compositeResidual e anomaly A L lift beta fields mixing primitive mu s p x =
      differentialPart beta fields (fun nu => liftedGamma A L lift nu s p x) mu +
      mixingAction mixing mu (fun output => liftedGamma A L lift mu s output x) p -
      quantumExactGamma e anomaly A L (primitive p) mu s x := rfl

theorem differentialPart_change (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (J K : ℝ → FormalAmplitude G) (c : ℝ → ℂ) (mu : ℝ)
    (hc : DifferentiableAt ℝ c mu) (hJ : ScaleDifferentiable J mu)
    (hK : ScaleDifferentiable K mu) :
    differentialPart beta fields (fun nu => J nu + c nu • amplitudeDelay (K nu)) mu =
      differentialPart beta fields J mu +
      c mu • amplitudeDelay (differentialPart beta fields K mu) +
      ((mu : ℂ) * deriv c mu) • amplitudeDelay (K mu) +
      (2 * c mu) • scalarAction beta (firstDelay (K mu)) := by
  have hcorr : ScaleDifferentiable (fun nu => c nu • amplitudeDelay (K nu)) mu := by
    intro r l legs q
    exact hc.mul (delay_differentiable K mu hK r l legs q)
  unfold differentialPart
  rw [scaleDerivative_add J _ mu hJ hcorr, scaleDerivative_smul_delay c K mu hc hK]
  simp only [couplingDerivative_add, couplingDerivative_smul, couplingDerivative_delay,
    scalarAction_add, scalarAction_smul, scalarAction_delay, fieldAction_add,
    fieldAction_smul, fieldAction_delay, amplitudeDelay_sub, amplitudeDelay_add]
  funext r l legs q
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem differentialPart_congr_nhds (beta : ScalarCoefficients) (fields : FieldCoefficients)
    (J K : ℝ → FormalAmplitude G) (mu : ℝ) (h : J =ᶠ[nhds mu] K) :
    differentialPart beta fields J mu = differentialPart beta fields K mu := by
  have h0 := h.eq_of_nhds
  have hs : scaleDerivative J mu = scaleDerivative K mu := by
    funext r l legs q
    have he : (fun nu => J nu r l legs q) =ᶠ[nhds mu] fun nu => K nu r l legs q :=
      h.mono (fun nu hh => congrFun (congrFun (congrFun (congrFun hh r) l) legs) q)
    exact congrArg (fun z : ℂ => (mu : ℂ)*z) he.deriv_eq
  simp only [differentialPart, h0, hs]

variable {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}

theorem family_scale_differentiable {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (mu : ℝ) (hmu : 0 < mu)
    (s : CutoffScales) (hs : mu < s.ultraviolet)
    (p : InvariantInsertionLabel G) (x : Spacetime) :
    ScaleDifferentiable (fun nu => liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale family.lift) nu s p x) mu := by
  intro r l legs q
  have ht := (N.same_scale_insertion.lifted_scale_smooth s p r l legs).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds (show (mu,(x,q)) ∈
      Set.Ioo 0 s.ultraviolet ×ˢ Set.univ from ⟨⟨hmu,hs⟩,Set.mem_univ _⟩))
  simpa only [Function.comp_def] using!
    ((ht.comp mu (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))

theorem family_differential_change (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0))
    (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (hs : mu < s.ultraviolet)
    (p : InvariantInsertionLabel G) (x : Spacetime) :
    let J := fun nu label => liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale family.lift) nu s label x
    let c := fun nu => (((positiveScaleExtension S.referenceScale a nu) * D.weight p : ℝ) : ℂ)
    differentialPart N.beta N.fields
      (fun nu => liftedGamma S.background S.insertions
        (positiveScaleExtension S.referenceScale (changeFamily family D a).lift) nu s p x) mu =
      differentialPart N.beta N.fields (fun nu => J nu p) mu +
      c mu • amplitudeDelay (differentialPart N.beta N.fields (fun nu => J nu D.lower) mu) +
      ((mu : ℂ) * deriv c mu) • amplitudeDelay (J mu D.lower) +
      (2*c mu) • scalarAction N.beta (firstDelay (J mu D.lower)) := by
  dsimp only
  have hc : DifferentiableAt ℝ
      (fun nu => (((positiveScaleExtension S.referenceScale a nu) * D.weight p : ℝ) : ℂ)) mu := by
    have ht := (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (ha.mul (contDiffOn_const (c := D.weight p)))).contDiffAt
      (Ioi_mem_nhds hmu)
    exact ht.differentiableAt (by simp)
  have he : (fun nu => liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale (changeFamily family D a).lift) nu s p x)
      =ᶠ[nhds mu]
      (fun nu => liftedGamma S.background S.insertions
        (positiveScaleExtension S.referenceScale family.lift) nu s p x +
        (((positiveScaleExtension S.referenceScale a nu) * D.weight p : ℝ) : ℂ) •
          amplitudeDelay (liftedGamma S.background S.insertions
            (positiveScaleExtension S.referenceScale family.lift) nu s D.lower x)) := by
    filter_upwards [Ioi_mem_nhds hmu] with nu hnu
    exact family_liftedGamma_change family D a nu hnu s p x
  rw [differentialPart_congr_nhds N.beta N.fields _ _ mu he]
  exact differentialPart_change N.beta N.fields _ _ _ mu hc
    (family_scale_differentiable N mu hmu s hs p x)
    (family_scale_differentiable N mu hmu s hs D.lower x)

/-- At the first potentially nonzero beta order, the coupling product rule
already contributes at g^4 hbar^2. It need not vanish for a scale-independent
finite correction. This uses the actual native beta guards. -/
theorem beta_correction_four_two {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (c : ℂ) (A : FormalAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    ((2*c) • scalarAction N.beta (firstDelay A)) 4 2 legs q =
      2*c*(N.beta 3 1 : ℂ)*A 0 0 legs q := by
  have hb0 (l : ℕ) : N.beta 0 l = 0 := N.same_scale_insertion.action.beta_free l 0 (by decide)
  have hb1 (l : ℕ) : N.beta 1 l = 0 := N.same_scale_insertion.action.beta_free l 1 (by decide)
  have hb2 (l : ℕ) : N.beta 2 l = 0 := N.same_scale_insertion.action.beta_free l 2 (by decide)
  norm_num [scalarAction, firstDelay, Fin.sum_univ_succ,
    N.same_scale_insertion.action.beta_classical, hb0, hb1, hb2, smul_eq_mul]
  ring

theorem beta_correction_four_two_ne_zero {family : LocalWardFlowFamily S}
    (N : GeneratedScaleNormalization family) (c : ℂ) (A : FormalAmplitude G)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hc : c ≠ 0) (hb : N.beta 3 1 ≠ 0) (hA : A 0 0 legs q ≠ 0) :
    ((2*c) • scalarAction N.beta (firstDelay A)) 4 2 legs q ≠ 0 := by
  rw [beta_correction_four_two]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hc)
    (Complex.ofReal_ne_zero.mpr hb)) hA

#print axioms beta_correction_four_two
#print axioms beta_correction_four_two_ne_zero
#print axioms amplitudeDelay_add
#print axioms amplitudeDelay_sub
#print axioms scalarAction_add
#print axioms scalarAction_smul
#print axioms scalarAction_delay
#print axioms fieldAction_add
#print axioms fieldAction_smul
#print axioms fieldAction_delay
#print axioms couplingDerivative_add
#print axioms couplingDerivative_smul
#print axioms couplingDerivative_delay
#print axioms delay_differentiable
#print axioms scaleDerivative_add
#print axioms scaleDerivative_smul_delay
#print axioms compositeResidual_parts
#print axioms differentialPart_change
#print axioms differentialPart_congr_nhds
#print axioms family_scale_differentiable
#print axioms family_differential_change
end YMYMG.ScaleTransport
