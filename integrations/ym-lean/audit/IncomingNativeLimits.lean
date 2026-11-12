import IncomingNativeExtractor
import IncomingWeakLimits

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! The changed coefficients are weak UV limits of the actual native
extractor. The proof is conditional on the old native regularity and limits. -/
noncomputable section
open MeasureTheory Filter
namespace YMYMG.IncomingExpansion
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization

variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}

theorem tupleJet_test_change {I : Type*} (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (h : S.LiftedCoefficientRegularity lift)
    (D : Direction G) (decode : I → InvariantInsertionLabel G) (lower : I)
    (hlower : decode lower = D.lower) (a : ℝ) {n : ℕ} (output : LocalMonomial G)
    (UV : ℝ) (hUV : S.referenceScale.val < UV) (f : OPE.RelativeTest n)
    (hf : OPE.MultiOffDiagonal f) (labels : Fin (n+1) → I) (order loop : ℕ)
    (r : OPE.RelativeSpace n) :
    tupleJet S (change lift D a) output UV r (fun i => decode (labels i)) order loop * f r =
      expandInputs jetDelay (fun p => ((a * D.weight (decode p) : ℝ) : ℂ)) lower (n+1)
        (fun xs k l => tupleJet S lift output UV r (fun i => decode (xs i)) k l * f r)
        labels order loop := by
  by_cases hr : f r = 0
  · simp only [hr, mul_zero]
    exact (congrFun (congrFun (expand_zero jetDelay _ lower (n+1) labels) order) loop).symm
  · have hs := hf.2 r (subset_tsupport f hr)
    rw [tupleJet_change S lift h D decode lower hlower a output UV r hUV hs.1 hs.2,
      expand_mul]

theorem tupleJet_test_integrable (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (h : S.LiftedCoefficientRegularity lift)
    (D : Direction G) (a : ℝ) {n : ℕ} (output : LocalMonomial G)
    (UV : ℝ) (hUV : S.referenceScale.val < UV) (f : OPE.RelativeTest n)
    (hf : OPE.MultiOffDiagonal f) (labels : Fin (n+1) → InvariantInsertionLabel G)
    (order loop : ℕ) :
    Integrable (fun r => tupleJet S (change lift D a) output UV r labels order loop * f r) := by
  have he (r : OPE.RelativeSpace n) :=
    tupleJet_test_change S lift h D id D.lower rfl a output UV hUV f hf labels order loop r
  simp only [id_eq] at he
  simp_rw [he]
  exact expand_integrable volume _ D.lower (n+1) _
    (fun xs k l => h.test_integrable n (fun i => xs i.castSucc) (xs (Fin.last n))
      output l k UV f hUV hf) labels order loop

/-- All three fields of the native regularity structure, including the
actual test-integrability condition, are transported. -/
theorem regularity_change (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (h : S.LiftedCoefficientRegularity lift)
    (D : Direction G) (a : ℝ) : S.LiftedCoefficientRegularity (change lift D a) := by
  constructor
  · intro n labels last output loop UV r hUV hzero hdistinct
    simpa only [nativeTuple, Fin.lastCases_castSucc, Fin.lastCases_last] using!
      nativeTuple_changed_smooth S lift h D a output UV r hUV hzero hdistinct
        (Fin.lastCases last labels) loop
  · intro n labels last output loop UV g r hUV hzero hdistinct
    simpa only [nativeTuple, Fin.lastCases_castSucc, Fin.lastCases_last] using!
      nativeTuple_changed_graph S lift h D a output UV r hUV hzero hdistinct
        (Fin.lastCases last labels) g loop
  · intro n labels last output loop order UV f hUV hf
    simpa only [tupleJet, Fin.lastCases_castSucc, Fin.lastCases_last] using!
      tupleJet_test_integrable S lift h D a output UV hUV f hf
        (Fin.lastCases last labels) order loop

theorem tupleJet_integral_change {I : Type*} (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (h : S.LiftedCoefficientRegularity lift)
    (D : Direction G) (decode : I → InvariantInsertionLabel G) (lower : I)
    (hlower : decode lower = D.lower) (a : ℝ) {n : ℕ} (output : LocalMonomial G)
    (UV : ℝ) (hUV : S.referenceScale.val < UV) (f : OPE.RelativeTest n)
    (hf : OPE.MultiOffDiagonal f) (labels : Fin (n+1) → I) (order loop : ℕ) :
    (∫ r, tupleJet S (change lift D a) output UV r (fun i => decode (labels i)) order loop * f r) =
      expandInputs jetDelay (fun p => ((a * D.weight (decode p) : ℝ) : ℂ)) lower (n+1)
        (fun xs k l => ∫ r, tupleJet S lift output UV r (fun i => decode (xs i)) k l * f r)
        labels order loop := by
  simp_rw [tupleJet_test_change S lift h D decode lower hlower a output UV hUV f hf]
  exact expand_integral volume _ lower (n+1) _
    (fun xs k l => h.test_integrable n (fun i => decode (xs i.castSucc))
      (decode (xs (Fin.last n))) output l k UV f hUV hf) labels order loop

theorem tupleJet_limit_change {I : Type*} (S : FixedFlowSystem e)
    (lift : QuantumObservableLift G) (h : S.LiftedCoefficientRegularity lift)
    (D : Direction G) (decode : I → InvariantInsertionLabel G) (lower : I)
    (hlower : decode lower = D.lower) (a : ℝ) {n : ℕ} (output : LocalMonomial G)
    (f : OPE.RelativeTest n) (hf : OPE.MultiOffDiagonal f)
    (limit : (Fin (n+1) → I) → ℕ → ℕ → ℂ)
    (hlimit : ∀ xs k l, Tendsto
      (fun UV => ∫ r, tupleJet S lift output UV r (fun i => decode (xs i)) k l * f r)
      atTop (nhds (limit xs k l)))
    (labels : Fin (n+1) → I) (order loop : ℕ) :
    Tendsto
      (fun UV => ∫ r, tupleJet S (change lift D a) output UV r
        (fun i => decode (labels i)) order loop * f r)
      atTop (nhds (expandInputs jetDelay (fun p => ((a * D.weight (decode p) : ℝ) : ℂ))
        lower (n+1) limit labels order loop)) := by
  have ht := expand_tendsto (fun p => ((a * D.weight (decode p) : ℝ) : ℂ)) lower (n+1)
    (fun xs UV k l => ∫ r, tupleJet S lift output UV r (fun i => decode (xs i)) k l * f r)
    limit hlimit labels order loop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop S.referenceScale.val] with UV hUV
  exact (tupleJet_integral_change S lift h D decode lower hlower a output UV hUV
    f hf labels order loop).symm

#print axioms tupleJet_test_change
#print axioms tupleJet_test_integrable
#print axioms regularity_change
#print axioms tupleJet_integral_change
#print axioms tupleJet_limit_change
end YMYMG.IncomingExpansion
