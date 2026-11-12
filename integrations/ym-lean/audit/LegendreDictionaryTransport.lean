import TupleJetShift
import ChangedFamilyLegendre

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Finite dictionary changes through the computed native Legendre recursion.
The background, ordered partitions, covariance and signs are unchanged. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.LegendreTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.Legendre YangMills.ScaleInsertion YangMills.LegendreInsertionBridge
open YMYMG.CouplingTaylor YMYMG.WordJet YMYMG.TupleJet
variable {G : CompactSimpleGaugeGroup}

def amplitudeDelay (A : FormalAmplitude G) : FormalAmplitude G :=
  fun r l legs q => delay (fun i j => A i j legs q) r l

def rootCoefficients (F : FormalAmplitude G) (s : CutoffScales)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (k : ℕ)
    (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (g h : Fin k → ℕ) : ℂ :=
  ∏ b : Fin k, meanFieldRoot F s (g b) (h b) (roots b)
    (selectedLegs legs (partitionBlock assignment b))
    (selectedMomenta legs (partitionBlock assignment b) q)

def partitionValue (A F : FormalAmplitude G) (s : CutoffScales) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (k : ℕ)
    (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) : ℂ :=
  ∑ g : Fin (k+1) → Fin (order+1), ∑ h : Fin (k+1) → Fin (loop+1),
    substitutionSummand A F s order loop legs q k assignment roots g h

theorem partitionValue_eq_tuple (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) :
    partitionValue A F s order loop legs q k assignment roots =
      if ∀ b, (partitionBlock assignment b).Nonempty then
        ((Nat.factorial k : ℂ)⁻¹ * partitionSign legs assignment) *
          tupleConvolve k (fun r l => A r l (rootLegs roots) (rootMomenta legs q assignment roots))
            (rootCoefficients F s legs q k assignment roots) order loop
      else 0 := by
  classical
  by_cases hb : ∀ b, (partitionBlock assignment b).Nonempty
  · simp only [partitionValue, substitutionSummand, hb, implies_true, true_and, if_true]
    simpa only [rootCoefficients, tupleConvolve, Finset.mul_sum, mul_assoc] using!
      (bounded_pair_eq_allocation (k+1) order loop (fun g h =>
      (Nat.factorial k : ℂ)⁻¹ * partitionSign legs assignment *
        A (g 0) (h 0) (rootLegs roots) (rootMomenta legs q assignment roots) *
          rootCoefficients F s legs q k assignment roots (fun i => g i.succ) (fun i => h i.succ)))
  · simp [partitionValue, substitutionSummand, hb]

theorem partitionValue_delay (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G) :
    partitionValue (amplitudeDelay A) F s order loop legs q k assignment roots =
      delay (fun r l => partitionValue A F s r l legs q k assignment roots) order loop := by
  classical
  simp only [partitionValue_eq_tuple, amplitudeDelay]
  by_cases hb : ∀ b, (partitionBlock assignment b).Nonempty
  · simp only [hb, implies_true, if_true, tupleConvolve_delay]
    exact map_delay
      (fun z : ℂ => ((Nat.factorial k : ℂ)⁻¹ * partitionSign legs assignment) * z)
      (by simp) _ order loop
  · simp only [hb, if_false]
    obtain order | order | order := order <;> cases loop <;> rfl

theorem meanFieldCompose_delay (A F : FormalAmplitude G) (s : CutoffScales) :
    meanFieldCompose (amplitudeDelay A) F s = amplitudeDelay (meanFieldCompose A F s) := by
  funext order loop legs q
  change (∑ k : Fin (legs.length+1), ∑ assignment : Fin legs.length → Fin k.val,
    ∑ roots : Fin k.val → ExternalLeg G,
      partitionValue (amplitudeDelay A) F s order loop legs q k.val assignment roots) =
    delay (fun r l => ∑ k : Fin (legs.length+1), ∑ assignment : Fin legs.length → Fin k.val,
      ∑ roots : Fin k.val → ExternalLeg G,
        partitionValue A F s r l legs q k.val assignment roots) order loop
  simp only [partitionValue_delay]
  obtain order | order | order := order <;> cases loop <;> simp [delay]

theorem substitutionSummand_add (A H F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (g : Fin (k+1) → Fin (order+1)) (h : Fin (k+1) → Fin (loop+1)) :
    substitutionSummand (A+H) F s order loop legs q k assignment roots g h =
      substitutionSummand A F s order loop legs q k assignment roots g h +
      substitutionSummand H F s order loop legs q k assignment roots g h := by
  unfold substitutionSummand
  split_ifs <;> simp [mul_add, add_mul]

theorem substitutionSummand_smul (c : ℂ) (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (k : ℕ) (assignment : Fin legs.length → Fin k) (roots : Fin k → ExternalLeg G)
    (g : Fin (k+1) → Fin (order+1)) (h : Fin (k+1) → Fin (loop+1)) :
    substitutionSummand (c • A) F s order loop legs q k assignment roots g h =
      c * substitutionSummand A F s order loop legs q k assignment roots g h := by
  unfold substitutionSummand
  split_ifs <;> simp [smul_eq_mul, mul_left_comm, mul_assoc]

theorem lowerComposition_add (A H F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    lowerComposition (A+H) F s order loop legs q =
      lowerComposition A F s order loop legs q + lowerComposition H F s order loop legs q := by
  simp only [lowerComposition, substitutionSummand_add, ite_add_zero,
    Finset.sum_add_distrib]

theorem lowerComposition_smul (c : ℂ) (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    lowerComposition (c • A) F s order loop legs q =
      c * lowerComposition A F s order loop legs q := by
  simp only [lowerComposition, substitutionSummand_smul, Finset.mul_sum,
    mul_ite, mul_zero]

def truncate (bound : ℕ) (A : FormalAmplitude G) : FormalAmplitude G :=
  fun r l legs q => if r < bound then A r l legs q else 0

theorem lowerComposition_eq_truncate (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    lowerComposition A F s order loop legs q =
      meanFieldCompose (truncate order A) F s order loop legs q := by
  unfold lowerComposition meanFieldCompose
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro assignment ha
  apply Finset.sum_congr rfl
  intro roots hr
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro h hh
  by_cases ht : (g 0).val < order
  · simp only [ht, if_true, substitutionSummand, truncate]
  · simp [ht, substitutionSummand, truncate]

theorem truncate_delay (A : FormalAmplitude G) (bound : ℕ) :
    truncate (bound+2) (amplitudeDelay A) = amplitudeDelay (truncate bound A) := by
  funext order loop legs q
  obtain order | order | order := order <;> cases loop
  all_goals simp [truncate, amplitudeDelay, delay]

theorem meanFieldCompose_zero (F : FormalAmplitude G) (s : CutoffScales) :
    meanFieldCompose 0 F s = 0 := by
  funext order loop legs q
  simp [meanFieldCompose, substitutionSummand]

theorem lowerComposition_delay (A F : FormalAmplitude G) (s : CutoffScales)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    lowerComposition (amplitudeDelay A) F s order loop legs q =
      delay (fun r l => lowerComposition A F s r l legs q) order loop := by
  rw [lowerComposition_eq_truncate]
  obtain order | order | order := order
  · have hz : truncate 0 (amplitudeDelay A) = 0 := by
      funext r l ls ps
      simp [truncate]
    rw [hz, meanFieldCompose_zero]
    rfl
  · have hz : truncate 1 (amplitudeDelay A) = 0 := by
      funext r l ls ps
      obtain r | r := r <;> simp [truncate, amplitudeDelay, delay]
    rw [hz, meanFieldCompose_zero]
    rfl
  · rw [truncate_delay, meanFieldCompose_delay]
    cases loop with
    | zero => simp only [amplitudeDelay, delay]
    | succ loop =>
      simpa only [amplitudeDelay, delay] using!
        (lowerComposition_eq_truncate A F s order loop legs q).symm

theorem insertion_add (F I J : FormalAmplitude G) (s : CutoffScales) :
    insertionGammaCoeff F (I+J) s = insertionGammaCoeff F I s + insertionGammaCoeff F J s := by
  have hall : ∀ order loop legs q,
      insertionGammaCoeff F (I+J) s order loop legs q =
        (insertionGammaCoeff F I s + insertionGammaCoeff F J s) order loop legs q := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro loop legs q
      have hl := lowerComposition_congr_prefix
        (insertionGammaCoeff F (I+J) s)
        (insertionGammaCoeff F I s + insertionGammaCoeff F J s) F s order loop legs q ih
      rw [insertionGammaCoeff_recurrence, hl, lowerComposition_add]
      simp only [Pi.add_apply, insertionGammaCoeff_recurrence]
      ring
  exact funext fun r => funext fun l => funext fun ls => funext fun ps => hall r l ls ps

theorem insertion_smul (c : ℂ) (F I : FormalAmplitude G) (s : CutoffScales) :
    insertionGammaCoeff F (c • I) s = c • insertionGammaCoeff F I s := by
  have hall : ∀ order loop legs q,
      insertionGammaCoeff F (c • I) s order loop legs q =
        (c • insertionGammaCoeff F I s) order loop legs q := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro loop legs q
      have hl := lowerComposition_congr_prefix
        (insertionGammaCoeff F (c • I) s) (c • insertionGammaCoeff F I s)
        F s order loop legs q ih
      rw [insertionGammaCoeff_recurrence, hl, lowerComposition_smul]
      simp only [Pi.smul_apply, smul_eq_mul, insertionGammaCoeff_recurrence]
      ring
  exact funext fun r => funext fun l => funext fun ls => funext fun ps => hall r l ls ps

theorem insertion_delay (F I : FormalAmplitude G) (s : CutoffScales) :
    insertionGammaCoeff F (amplitudeDelay I) s = amplitudeDelay (insertionGammaCoeff F I s) := by
  have hall : ∀ order loop legs q,
      insertionGammaCoeff F (amplitudeDelay I) s order loop legs q =
        amplitudeDelay (insertionGammaCoeff F I s) order loop legs q := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro loop legs q
      have hl := lowerComposition_congr_prefix
        (insertionGammaCoeff F (amplitudeDelay I) s)
        (amplitudeDelay (insertionGammaCoeff F I s)) F s order loop legs q ih
      rw [insertionGammaCoeff_recurrence, hl, lowerComposition_delay]
      obtain order | order | order := order <;> cases loop
      all_goals simp only [amplitudeDelay, delay, sub_zero, insertionGammaCoeff_recurrence]
  exact funext fun r => funext fun l => funext fun ls => funext fun ps => hall r l ls ps

open YMYMG.DictionaryRenormalization
open scoped ContDiff

theorem flowJet_change {lift : QuantumObservableLift G} {L : ℝ → InsertedFlowFamily G}
    {W : WardContinuumData G} (hl : lift.LimitCompatible L W) (D : Direction G) (a : ℝ)
    (p : InvariantInsertionLabel G) (x : Spacetime) (s : CutoffScales) :
    flowJet (fun g => (change lift D a).finiteInsertion (L g) g p x) s =
      flowJet (fun g => lift.finiteInsertion (L g) g p x) s +
      ((a * D.weight p : ℝ) : ℂ) •
        amplitudeDelay (flowJet (fun g => lift.finiteInsertion (L g) g D.lower x) s) := by
  funext order loop legs q
  simpa only [flowJet, finiteValue, jet, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    amplitudeDelay] using!
    (finiteValue_change hl D a p x s.infrared s.ultraviolet s.infrared_pos s.ordered
      legs q order loop)

theorem liftedGamma_change (A : ScaleCouplingFamily G)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (mu : ℝ) {W : WardContinuumData G} (hl : (lift mu).LimitCompatible (L mu) W)
    (D : Direction G) (a : ℝ → ℝ) (s : CutoffScales) (p : InvariantInsertionLabel G)
    (x : Spacetime) :
    liftedGamma A L (fun nu => change (lift nu) D (a nu)) mu s p x =
      liftedGamma A L lift mu s p x + ((a mu * D.weight p : ℝ) : ℂ) •
        amplitudeDelay (liftedGamma A L lift mu s D.lower x) := by
  simp only [liftedGamma, directionalGamma]
  rw [flowJet_change hl D (a mu) p x s, insertion_add, insertion_smul, insertion_delay]

variable {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}

theorem positiveScale_change (family : LocalWardFlowFamily S)
    (D : Direction G) (a : RenormalizationScale → ℝ) (mu : ℝ) :
    positiveScaleExtension S.referenceScale (changeFamily family D a).lift mu =
      change (positiveScaleExtension S.referenceScale family.lift mu) D
        (positiveScaleExtension S.referenceScale a mu) := by
  classical
  by_cases hmu : 0 < mu <;> simp [positiveScaleExtension, changeFamily, hmu]

theorem family_liftedGamma_change (family : LocalWardFlowFamily S)
    (D : Direction G) (a : RenormalizationScale → ℝ) (mu : ℝ) (hmu : 0 < mu)
    (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime) :
    liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale (changeFamily family D a).lift) mu s p x =
    liftedGamma S.background S.insertions
      (positiveScaleExtension S.referenceScale family.lift) mu s p x +
      (((positiveScaleExtension S.referenceScale a mu) * D.weight p : ℝ) : ℂ) •
        amplitudeDelay (liftedGamma S.background S.insertions
          (positiveScaleExtension S.referenceScale family.lift) mu s D.lower x) := by
  have he := funext (positiveScale_change family D a)
  rw [he]
  apply liftedGamma_change
  simpa only [positiveScaleExtension, dif_pos hmu] using!
    (family.full_ward ⟨mu,hmu⟩).same_dictionary_limit

/-- The exact joint scale/position/momentum smoothness field for the
changed family. Smoothness of the scale-dependent finite coefficient is
required explicitly, and the original normalization supplies old smoothness. -/
theorem changeFamily_scale_smooth (family : LocalWardFlowFamily S)
    (N : GeneratedScaleNormalization family) (D : Direction G)
    (a : RenormalizationScale → ℝ)
    (ha : ContDiffOn ℝ ∞ (positiveScaleExtension S.referenceScale a) (Set.Ioi 0))
    (s : CutoffScales) (p : InvariantInsertionLabel G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × (Spacetime × (Fin legs.length → Spacetime)) =>
        liftedGamma S.background S.insertions
          (positiveScaleExtension S.referenceScale (changeFamily family D a).lift)
          z.1 s p z.2.1 order loop legs z.2.2)
      (Set.Ioo 0 s.ultraviolet ×ˢ Set.univ) := by
  let J := liftedGamma S.background S.insertions
    (positiveScaleExtension S.referenceScale family.lift)
  have hc : ContDiffOn ℝ ∞
      (fun z : ℝ × (Spacetime × (Fin legs.length → Spacetime)) =>
        (((positiveScaleExtension S.referenceScale a z.1) * D.weight p : ℝ) : ℂ))
      (Set.Ioo 0 s.ultraviolet ×ˢ Set.univ) := by
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((ha.comp contDiffOn_fst (fun z hz => hz.1.1)).mul contDiffOn_const)
  have hd : ContDiffOn ℝ ∞
      (fun z : ℝ × (Spacetime × (Fin legs.length → Spacetime)) =>
        amplitudeDelay (J z.1 s D.lower z.2.1) order loop legs z.2.2)
      (Set.Ioo 0 s.ultraviolet ×ˢ Set.univ) := by
    obtain order | order | order := order <;> cases loop
    all_goals first
      | exact contDiffOn_const
      | exact N.same_scale_insertion.lifted_scale_smooth s D.lower _ _ legs
  apply ((N.same_scale_insertion.lifted_scale_smooth s p order loop legs).add (hc.mul hd)).congr
  intro z hz
  have he := congrFun (congrFun (congrFun (congrFun
    (family_liftedGamma_change family D a z.1 hz.1.1 s p z.2.1) order) loop) legs) z.2.2
  exact he

#print axioms flowJet_change
#print axioms liftedGamma_change
#print axioms positiveScale_change
#print axioms family_liftedGamma_change
#print axioms changeFamily_scale_smooth
#print axioms partitionValue_eq_tuple
#print axioms partitionValue_delay
#print axioms meanFieldCompose_delay
#print axioms substitutionSummand_add
#print axioms substitutionSummand_smul
#print axioms lowerComposition_add
#print axioms lowerComposition_smul
#print axioms lowerComposition_eq_truncate
#print axioms truncate_delay
#print axioms meanFieldCompose_zero
#print axioms lowerComposition_delay
#print axioms insertion_add
#print axioms insertion_smul
#print axioms insertion_delay
end YMYMG.LegendreTransport
