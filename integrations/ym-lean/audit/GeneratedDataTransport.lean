import IncomingRecoveryCoherent
import IncomingPhysicalBounds

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Transport every field of native GeneratedEuclideanData.Compatible
through a distinct, positive, equal-degree coordinate change. This is a
conditional theorem about existing native data, not a construction of the
starting Yang--Mills family or of its continuum asymptotic matching. -/
noncomputable section
namespace YMYMG.GeneratedDataTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization YMYMG.IncomingExpansion
open YMYMG.GeneratedIncomingRaw YMYMG.GeneratedOutputTransport
open YMYMG.IncomingPhysicalBounds YMYMG.IncomingRecovery YMYMG.OutputRecoveryCoherent

def evaluateCoordinate {I : Type*} (i : I) :
    (ℕ → ℕ → I → ℂ) →ₗ[ℂ] (ℕ → ℕ → ℂ) where
  toFun F r l := F r l i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluateCoordinate_delay {I : Type*} (i : I) (F : ℕ → ℕ → I → ℂ) :
    evaluateCoordinate i (jetDelay F) = jetDelay (evaluateCoordinate i F) := by
  funext r l
  exact vector_delay_apply F r l i

theorem expand_coordinate {I J : Type*} (w : I → ℂ) (lower : I) (n : ℕ)
    (F : (Fin n → I) → ℕ → ℕ → J → ℂ) (labels : Fin n → I) (r l : ℕ) (j : J) :
    expandInputs jetDelay w lower n F labels r l j =
      expandInputs jetDelay w lower n (fun xs a b => F xs a b j) labels r l := by
  exact congrFun (congrFun (expand_natural jetDelay jetDelay (evaluateCoordinate j)
    (evaluateCoordinate_delay j) w lower n F labels) r) l

def inputWeight {I : Type*} [DecidableEq I] (high : I) (a : ℝ) (p : I) : ℂ :=
  if p = high then (a : ℂ) else 0

variable {G : CompactSimpleGaugeGroup} {basis : OPE.FilteredBasis G}

def changeGenerated (E : GeneratedEuclideanData basis) (high low : basis.Index)
    (a : ℝ) : GeneratedEuclideanData basis where
  raw := incomingRaw E (inputWeight high a) low
  physical := incomingPhysical (changeOutputs E high low a) (inputWeight high a) low

theorem inputWeight_degree (high low : basis.Index)
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ)
    (p : basis.Index) (hp : inputWeight high a p ≠ 0) :
    OPE.dimension (basis.label low) = OPE.dimension (basis.label p) := by
  by_cases he : p = high
  · simpa only [he] using hd
  · exact False.elim (hp (by simp only [inputWeight, if_neg he]))

theorem inputWeight_direction (high low : basis.Index)
    (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ) :
    (fun p => ((a * (coordinateDirectionLE basis high low hpos hd.le).weight (basis.label p) : ℝ) : ℂ)) =
      inputWeight high a := by
  funext p
  rw [directionLE_weights]
  by_cases hp : p = high <;> simp [inputWeight, hp]

variable {B : InvariantForm G} {e : ColorFrame B} {S : FixedFlowSystem e}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}
    {transport : SameTheoryWardTransportData e (S.insertions S.referenceScale.val)}

theorem combined_recovery (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (high low : basis.Index)
    (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ)
    (n : ℕ) (inputs : Fin n → basis.Index) (last : basis.Index) (cutoff : ℕ)
    (f : OPE.RelativeTest n) (hf : OPE.MultiOffDiagonal f) :
    ∃ count : ℕ, ∃ index : Fin count → basis.Index,
      Function.Injective index ∧ Finset.univ.image index = basis.active cutoff ∧
      QuantumPhysicalOutputRecovery e (S.insertions S.referenceScale.val) transport
        (change lift (coordinateDirectionLE basis high low hpos hd.le) a) W Q cutoff
        (fun i => basis.label (index i))
        (fun r l m => (changeGenerated E high low a).raw r l n inputs last m f)
        (fun r l i => (changeGenerated E high low a).physical r l n inputs last (index i) f) := by
  let labels : Fin (n+1) → basis.Index := Fin.lastCases last inputs
  let raw := fun (xs : Fin (n+1) → basis.Index) r l m =>
    E.raw r l n (fun i => xs i.castSucc) (xs (Fin.last n)) m f
  let c := fun (xs : Fin (n+1) → basis.Index) r l i =>
    (changeOutputs E high low a).physical r l n (fun j => xs j.castSucc) (xs (Fin.last n)) i f
  have hold (xs : Fin (n+1) → basis.Index) :
      CoherentRecovery basis e (S.insertions S.referenceScale.val) transport
        (change lift (coordinateDirectionLE basis high low hpos hd.le) a) W Q (raw xs) (c xs) := by
    intro D
    exact outputs_recovery E h high low hne hpos hd a n
      (fun i => xs i.castSucc) (xs (Fin.last n)) D f hf
  have hnew := expand_recovery basis (inputWeight high a) low (n+1) raw c hold labels
  have hr : expandInputs jetDelay (inputWeight high a) low (n+1) raw labels =
      fun r l m => (changeGenerated E high low a).raw r l n inputs last m f := by
    funext r l m
    rw [expand_coordinate]
    exact (incomingRaw_apply E (inputWeight high a) low r l n inputs last m f).symm
  have hc : expandInputs jetDelay (inputWeight high a) low (n+1) c labels =
      fun r l i => (changeGenerated E high low a).physical r l n inputs last i f := by
    funext r l i
    rw [expand_coordinate]
    exact (incomingPhysical_apply (changeOutputs E high low a) (inputWeight high a)
      low r l n inputs last i f).symm
  rw [hr, hc] at hnew
  exact hnew cutoff

/-- The complete native structure: both incoming and outgoing data change
together, while the flow, Ward limit and source transport stay fixed. -/
theorem compatible_change (E : GeneratedEuclideanData basis)
    (h : E.Compatible S lift W Q transport) (high low : basis.Index)
    (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ) :
    (changeGenerated E high low a).Compatible S
      (change lift (coordinateDirectionLE basis high low hpos hd.le) a) W Q transport := by
  constructor
  · exact h.same_flow_continuum
  · exact regularity_change S lift h.regularity _ a
  · exact incomingRaw_local E h.raw_local (inputWeight high a) low
  · intro r l n inputs last output f hf
    have ht := incomingRaw_limit E h (coordinateDirectionLE basis high low hpos hd.le)
      low rfl a r l n inputs last output f hf
    rw [inputWeight_direction high low hpos hd a] at ht
    exact ht
  · intro r l n inputs last output
    exact expand_local (inputWeight high a) low (n+1) _
      (fun xs k j => outputs_local E h high low a k j n
        (fun i => xs i.castSucc) (xs (Fin.last n)) output) _ r l
  · intro r l n inputs last output hrl
    exact expand_graph (inputWeight high a) low (n+1) _
      (fun xs k j hkj => outputs_graph E h high low a k j n
        (fun i => xs i.castSucc) (xs (Fin.last n)) output hkj) _ r l hrl
  · exact incomingPhysical_scaling (changeOutputs E high low a)
      (outputs_scaling E h high low hd a) (inputWeight high a) low
      (inputWeight_degree high low hd a)
  · exact combined_recovery E h high low hne hpos hd a

/-- Existence of a full native generated-data witness is invariant under
this coordinate change. The original witness is still an explicit premise. -/
theorem compatible_exists_iff (high low : basis.Index)
    (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (a : ℝ) :
    (∃ E : GeneratedEuclideanData basis, E.Compatible S
      (change lift (coordinateDirectionLE basis high low hpos hd.le) a) W Q transport) ↔
    (∃ E : GeneratedEuclideanData basis, E.Compatible S lift W Q transport) := by
  have hq : (coordinateDirectionLE basis high low hpos hd.le).weight
      (coordinateDirectionLE basis high low hpos hd.le).lower = 0 := by
    change (coordinateDirectionLE basis high low hpos hd.le).weight (basis.label low) = 0
    rw [directionLE_weights]
    exact if_neg (Ne.symm hne)
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨changeGenerated E high low (-a), ?_⟩
    have ht := compatible_change E hE high low hne hpos hd (-a)
    simpa only [change_inverse _ a hq] using ht
  · rintro ⟨E, hE⟩
    exact ⟨changeGenerated E high low a, compatible_change E hE high low hne hpos hd a⟩

#print axioms evaluateCoordinate
#print axioms evaluateCoordinate_delay
#print axioms expand_coordinate
#print axioms inputWeight_degree
#print axioms inputWeight_direction
#print axioms combined_recovery
#print axioms compatible_change
#print axioms compatible_exists_iff
end YMYMG.GeneratedDataTransport
