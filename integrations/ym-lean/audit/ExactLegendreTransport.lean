import PrimitiveTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! The primitive correction through the actual coupling jets and recursive
Legendre transform. All needed coupling smoothness comes from the native
fixed family and the primitive graph grading. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.ExactTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre
open YMYMG.DictionaryRenormalization YMYMG.CouplingTaylor YMYMG.LegendreTransport
variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
  {S : FixedFlowSystem e}

theorem family_exactFlowJet_change (family : LocalWardFlowFamily S)
    (P : (p : InvariantInsertionLabel G) → LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (D : Direction G) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime) :
    let anomaly := positiveScaleExtension S.referenceScale
      (fun scale => (family.singleTransport scale).coefficient)
    flowJet (fun g => quantumExactInsertion e anomaly S.insertions
      (changePrimitive P D a ha p) mu g x) s =
      flowJet (fun g => quantumExactInsertion e anomaly S.insertions (P p) mu g x) s +
      ((a mu*D.weight p : ℝ) : ℂ) • amplitudeDelay
        (flowJet (fun g => quantumExactInsertion e anomaly S.insertions (P D.lower) mu g x) s) := by
  dsimp only
  let anomaly := positiveScaleExtension S.referenceScale
    (fun scale => (family.singleTransport scale).coefficient)
  have hc (label : InvariantInsertionLabel G) (loop : ℕ)
      (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
      ContDiff ℝ ∞ (fun g => quantumExactInsertion e anomaly S.insertions
        (P label) mu g x loop s.infrared s.ultraviolet legs q) :=
    family_exactInsertion_smooth family (P label) mu hmu x loop s legs q
  funext r l legs q
  change jet r (fun g => quantumExactInsertion e anomaly S.insertions
      (changePrimitive P D a ha p) mu g x l s.infrared s.ultraviolet legs q) =
    jet r (fun g => quantumExactInsertion e anomaly S.insertions
      (P p) mu g x l s.infrared s.ultraviolet legs q) +
    ((a mu*D.weight p : ℝ) : ℂ) * delay
      (fun i j => jet i (fun g => quantumExactInsertion e anomaly S.insertions
        (P D.lower) mu g x j s.infrared s.ultraviolet legs q)) r l
  cases l with
  | zero => simp [exactInsertion_change_zero, delay]
  | succ l =>
    simp only [exactInsertion_change_succ]
    have hs : ContDiff ℝ ∞ (fun g : ℝ => (g : ℂ)^2 * (a mu*D.weight p : ℝ) *
        quantumExactInsertion e anomaly S.insertions (P D.lower) mu g x l
          s.infrared s.ultraviolet legs q) :=
      ((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul (hc D.lower l legs q)
    rw [jet_add _ _ _ (hc p (l+1) legs q) hs]
    have he : (fun g : ℝ => (g : ℂ)^2 * (a mu*D.weight p : ℝ) *
        quantumExactInsertion e anomaly S.insertions (P D.lower) mu g x l
          s.infrared s.ultraviolet legs q) =
        fun g : ℝ => (a mu*D.weight p : ℝ) * ((g : ℂ)^2 *
          quantumExactInsertion e anomaly S.insertions (P D.lower) mu g x l
            s.infrared s.ultraviolet legs q) := by funext g; ring
    rw [he, jet_const_mul, jet_mul_square _ _ (hc D.lower l legs q)]
    obtain r | r | r := r <;> simp [delay]

theorem family_exactGamma_change (family : LocalWardFlowFamily S)
    (P : (p : InvariantInsertionLabel G) → LocalScalePrimitive G (intrinsicEngineeringDimension p) 0)
    (D : Direction G) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (mu : ℝ) (hmu : 0 < mu) (s : CutoffScales) (p : InvariantInsertionLabel G) (x : Spacetime) :
    let anomaly := positiveScaleExtension S.referenceScale
      (fun scale => (family.singleTransport scale).coefficient)
    quantumExactGamma e anomaly S.background S.insertions (changePrimitive P D a ha p) mu s x =
      quantumExactGamma e anomaly S.background S.insertions (P p) mu s x +
      ((a mu*D.weight p : ℝ) : ℂ) • amplitudeDelay
        (quantumExactGamma e anomaly S.background S.insertions (P D.lower) mu s x) := by
  dsimp only
  simp only [quantumExactGamma, directionalGamma]
  rw [family_exactFlowJet_change family P D a ha mu hmu s p x,
    insertion_add, insertion_smul, insertion_delay]

#print axioms family_exactFlowJet_change
#print axioms family_exactGamma_change
end YMYMG.ExactTransport
