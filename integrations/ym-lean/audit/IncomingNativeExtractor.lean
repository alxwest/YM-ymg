import IncomingFiniteTransport
import IncomingTaylorTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Bind the finite multilinear identity to the actual same-system OPE
extractor, including the anchored last insertion and its coupling jets. -/
noncomputable section
open scoped ContDiff
namespace YMYMG.IncomingExpansion
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization

variable {G : CompactSimpleGaugeGroup}

def evaluateState (acc : List (PositionedInsertion G)) :
    FiniteState G →ₗ[ℂ] (ℕ → ℂ) where
  toFun F loop := F loop acc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluateState_delay (acc : List (PositionedInsertion G)) (F : FiniteState G) :
    evaluateState acc (loopDelay F) = loopDelay (evaluateState acc F) := by
  funext loop
  cases loop <;> rfl

theorem finiteWord_change_value {I : Type*} (lift : QuantumObservableLift G) (D : Direction G)
    (decode : I → InvariantInsertionLabel G) (lower : I) (hlower : decode lower = D.lower)
    (a g UV : ℝ) (n : ℕ) (positions : Fin n → Spacetime) (labels : Fin n → I)
    (F : FiniteState G) (loop : ℕ) (acc : List (PositionedInsertion G)) :
    finiteWord (change lift D a) g UV positions (fun i => decode (labels i)) F loop acc =
      expandInputs loopDelay (fun p => (g : ℂ)^2 * ((a * D.weight (decode p) : ℝ) : ℂ))
        lower n (fun xs l => finiteWord lift g UV positions (fun i => decode (xs i)) F l acc)
        labels loop := by
  have h := congrArg (evaluateState acc)
    (finiteWord_change lift D decode lower hlower a g UV n positions labels F)
  rw [expand_natural loopDelay loopDelay (evaluateState acc) (evaluateState_delay acc)] at h
  exact congrFun h loop

variable {B : InvariantForm G} {e : ColorFrame B}

def nativeBase (S : FixedFlowSystem e) (output : LocalMonomial G) (g UV : ℝ) : FiniteState G :=
  fun remaining raw => match insertionClusterOfList raw with
    | none => 0
    | some cluster => regulatedOPECoefficient (S.insertions S.referenceScale.val g)
        (S.oversubtractions S.referenceScale.val g) S.referenceScale.val UV cluster remaining output

def nativeTuple (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    {n : ℕ} (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (g : ℝ) (loop : ℕ) : ℂ :=
  S.liftedRegulatedCoefficient lift (fun i => labels i.castSucc) (labels (Fin.last n)) output loop g UV r

theorem nativeTuple_word (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    {n : ℕ} (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (g : ℝ) (loop : ℕ) :
    nativeTuple S lift output UV r labels g loop =
      finiteWord lift g UV (Fin.lastCases 0 r) labels (nativeBase S output g UV) loop [] := by
  rw [finiteWord_native]
  simp only [nativeTuple, FixedFlowSystem.liftedRegulatedCoefficient,
    liftedRegulatedOPECoefficient, relativeLiftedCluster, LiftedInsertionCluster.insertions,
    List.ofFn_succ', Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append]
  rfl

theorem nativeTuple_change {I : Type*} (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    (D : Direction G) (decode : I → InvariantInsertionLabel G) (lower : I)
    (hlower : decode lower = D.lower) (a : ℝ) {n : ℕ} (output : LocalMonomial G)
    (UV : ℝ) (r : OPE.RelativeSpace n) (labels : Fin (n+1) → I) (g : ℝ) (loop : ℕ) :
    nativeTuple S (change lift D a) output UV r (fun i => decode (labels i)) g loop =
      finiteTransform (fun p => a * D.weight (decode p)) lower (n+1)
        (fun xs g l => nativeTuple S lift output UV r (fun i => decode (xs i)) g l) labels g loop := by
  simpa only [nativeTuple_word, finiteTransform] using!
    finiteWord_change_value lift D decode lower hlower a g UV (n+1)
      (Fin.lastCases 0 r) labels (nativeBase S output g UV) loop []

theorem nativeTuple_smooth (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    (h : S.LiftedCoefficientRegularity lift) {n : ℕ} (output : LocalMonomial G)
    (UV : ℝ) (r : OPE.RelativeSpace n) (hUV : S.referenceScale.val < UV)
    (hzero : ∀ i, r i ≠ 0) (hdistinct : ∀ i j, i ≠ j → r i ≠ r j)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (loop : ℕ) :
    ContDiff ℝ ∞ (fun g => nativeTuple S lift output UV r labels g loop) :=
  h.coupling_smooth n _ _ output loop UV r hUV hzero hdistinct

theorem nativeTuple_changed_smooth (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    (h : S.LiftedCoefficientRegularity lift) (D : Direction G) (a : ℝ) {n : ℕ}
    (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (hUV : S.referenceScale.val < UV) (hzero : ∀ i, r i ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → r i ≠ r j)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (loop : ℕ) :
    ContDiff ℝ ∞ (fun g => nativeTuple S (change lift D a) output UV r labels g loop) := by
  have he (g : ℝ) := nativeTuple_change S lift D id D.lower rfl a output UV r labels g loop
  simp only [id_eq] at he
  simp_rw [he]
  exact finiteTransform_smooth _ D.lower (n+1) _
    (nativeTuple_smooth S lift h output UV r hUV hzero hdistinct) labels loop

theorem nativeTuple_changed_graph (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    (h : S.LiftedCoefficientRegularity lift) (D : Direction G) (a : ℝ) {n : ℕ}
    (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (hUV : S.referenceScale.val < UV) (hzero : ∀ i, r i ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → r i ≠ r j)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (g : ℝ) (loop : ℕ) :
    nativeTuple S (change lift D a) output UV r labels g loop =
      (g : ℂ)^(output.legs.length+2*loop) *
        nativeTuple S (change lift D a) output UV r labels 1 loop := by
  have he (g : ℝ) := nativeTuple_change S lift D id D.lower rfl a output UV r labels g loop
  simp only [id_eq] at he
  rw [he g, he 1]
  exact finiteTransform_graph (fun p => a * D.weight p) D.lower (n+1)
    (fun xs g l => nativeTuple S lift output UV r xs g l) output.legs.length
    (fun xs g l => h.graph_grading n (fun i => xs i.castSucc) (xs (Fin.last n))
      output l UV g r hUV hzero hdistinct) labels g loop

def tupleJet (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    {n : ℕ} (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (order loop : ℕ) : ℂ :=
  S.liftedCouplingCoefficient lift (fun i => labels i.castSucc) (labels (Fin.last n)) output loop order UV r

theorem tupleJet_eq_jet (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    {n : ℕ} (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (labels : Fin (n+1) → InvariantInsertionLabel G) (order loop : ℕ) :
    tupleJet S lift output UV r labels order loop =
      jet order (fun g => nativeTuple S lift output UV r labels g loop) := rfl

theorem tupleJet_change {I : Type*} (S : FixedFlowSystem e) (lift : QuantumObservableLift G)
    (h : S.LiftedCoefficientRegularity lift) (D : Direction G)
    (decode : I → InvariantInsertionLabel G) (lower : I) (hlower : decode lower = D.lower)
    (a : ℝ) {n : ℕ} (output : LocalMonomial G) (UV : ℝ) (r : OPE.RelativeSpace n)
    (hUV : S.referenceScale.val < UV) (hzero : ∀ i, r i ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → r i ≠ r j)
    (labels : Fin (n+1) → I) (order loop : ℕ) :
    tupleJet S (change lift D a) output UV r (fun i => decode (labels i)) order loop =
      expandInputs jetDelay (fun p => ((a * D.weight (decode p) : ℝ) : ℂ)) lower (n+1)
        (fun xs => tupleJet S lift output UV r (fun i => decode (xs i))) labels order loop := by
  simp only [tupleJet_eq_jet, nativeTuple_change S lift D decode lower hlower a]
  exact finiteTransform_jet _ lower (n+1) _
    (fun xs l => nativeTuple_smooth S lift h output UV r hUV hzero hdistinct _ l) labels order loop

#print axioms evaluateState
#print axioms evaluateState_delay
#print axioms finiteWord_change_value
#print axioms nativeTuple_word
#print axioms nativeTuple_change
#print axioms nativeTuple_smooth
#print axioms nativeTuple_changed_smooth
#print axioms nativeTuple_changed_graph
#print axioms tupleJet_eq_jet
#print axioms tupleJet_change
end YMYMG.IncomingExpansion
