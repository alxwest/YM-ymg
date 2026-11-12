import OutputRecoveryExact
import OutputRecoveryCutoffs

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! A common outgoing coefficient table for elementary coordinate changes.
When the two selected labels enter every cutoff together, the same table
works at every cutoff. Equal engineering degrees imply that condition.
Incoming raw limits, locality and power counting are separate obligations. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.OutputRecoveryCoherent
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.DictionaryRenormalization
open YMYMG.OutputRecovery YMYMG.OutputRecoveryCutoffs

def coordinateCorrection {I : Type*} [DecidableEq I] (high low : I) (a : ℝ)
    (c : ℕ → ℕ → I → ℂ) : ℕ → ℕ → I → ℂ :=
  fun order loop i => c order loop i -
    if i = low then (a : ℂ) * delay (fun r l => c r l high) order loop else 0

theorem coordinateCorrection_graph {I : Type*} [DecidableEq I]
    (high low : I) (a : ℝ) (c : ℕ → ℕ → I → ℂ)
    (hc : ∀ order loop i, order < 2*loop → c order loop i = 0)
    (order loop : ℕ) (i : I) (h : order < 2*loop) :
    coordinateCorrection high low a c order loop i = 0 := by
  have hd : delay (fun r l => c r l high) order loop = 0 := by
    obtain order | order | order := order <;> cases loop
    all_goals simp only [delay]
    exact hc _ _ high (by omega)
  simp [coordinateCorrection, hc _ _ _ h, hd]

theorem coordinateCorrection_inverse {I : Type*} [DecidableEq I]
    (high low : I) (hne : high ≠ low) (a : ℝ) (c : ℕ → ℕ → I → ℂ) :
    coordinateCorrection high low (-a) (coordinateCorrection high low a c) = c := by
  funext order loop i
  by_cases hi : i = low <;> simp [coordinateCorrection, hi, hne]

theorem weightedOn_coordinate {I : Type*} [DecidableEq I]
    (active : Finset I) (high : I) (w : I → ℝ)
    (hw : ∀ i, w i = if i = high then 1 else 0)
    (c : ℕ → ℕ → I → ℂ) (hhigh : high ∈ active) :
    weightedOn active w c = fun r l => c r l high := by
  funext order loop
  simp [weightedOn, hw, apply_ite, hhigh]

theorem correction_enumerated_active {I : Type*} [DecidableEq I] {n : ℕ}
    (index : Fin n → I) (hinj : Function.Injective index) (high low : I)
    (w : I → ℝ) (hw : ∀ i, w i = if i = high then 1 else 0)
    (k : Fin n) (hk : index k = low) (hhigh : high ∈ Finset.univ.image index)
    (a : ℝ) (c : ℕ → ℕ → I → ℂ) :
    corrected (fun i => w (index i)) k a (fun r l i => c r l (index i)) =
      fun r l i => coordinateCorrection high low a c r l (index i) := by
  funext order loop i
  rw [corrected_enumeration index hinj]
  simp only [correctedOn, coordinateCorrection, hk,
    weightedOn_coordinate _ high w hw c hhigh]

theorem correction_enumerated_inactive {I : Type*} [DecidableEq I] {n : ℕ}
    (index : Fin n → I) (high low : I) (a : ℝ) (c : ℕ → ℕ → I → ℂ)
    (hlow : low ∉ Finset.univ.image index) :
    (fun r l i => coordinateCorrection high low a c r l (index i)) =
      fun r l i => c r l (index i) := by
  funext order loop i
  have hi : index i ≠ low := by
    intro h
    exact hlow (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  simp [coordinateCorrection, hi]

theorem weights_enumerated_inactive {I : Type*} [DecidableEq I] {n : ℕ}
    (index : Fin n → I) (high : I) (w : I → ℝ)
    (hw : ∀ i, w i = if i = high then 1 else 0)
    (hhigh : high ∉ Finset.univ.image index) : ∀ i, w (index i) = 0 := by
  intro i
  have hi : index i ≠ high := by
    intro h
    exact hhigh (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  simp [hw, hi]

variable {G : CompactSimpleGaugeGroup} {B : InvariantForm G} {e : ColorFrame B}
    {L : ℝ → InsertedFlowFamily G} {transport : SameTheoryWardTransportData e L}
    {lift : QuantumObservableLift G} {W : WardContinuumData G} {Q : QuantumWardLimit G}

/-- Both selected labels are active or both inactive. The common coefficient
table then gives the full native recovery relation, with the original raw
vector and exact primitive retained. -/
theorem sector_recovery (basis : OPE.FilteredBasis G) (D : Direction G)
    (high low : basis.Index) (hne : high ≠ low)
    (hlower : D.lower = basis.label low)
    (hw : ∀ i, D.weight (basis.label i) = if i = high then 1 else 0)
    (a : ℝ) (cutoff : ℕ) {n : ℕ} (index : Fin n → basis.Index)
    (hinj : Function.Injective index) (hactive : Finset.univ.image index = basis.active cutoff)
    (hjoint : high ∈ basis.active cutoff ↔ low ∈ basis.active cutoff)
    (raw : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ)
    (hold : QuantumPhysicalOutputRecovery e L transport lift W Q cutoff
      (fun i => basis.label (index i)) raw (fun r l i => c r l (index i))) :
    QuantumPhysicalOutputRecovery e L transport (change lift D a) W Q cutoff
      (fun i => basis.label (index i)) raw
      (fun r l i => coordinateCorrection high low a c r l (index i)) := by
  classical
  have hq : D.weight D.lower = 0 := by simp [hlower, hw, Ne.symm hne]
  by_cases hlow : low ∈ basis.active cutoff
  · have hhigh : high ∈ Finset.univ.image index := by rw [hactive]; exact hjoint.mpr hlow
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hactive.symm ▸ hlow)
    have hkl : basis.label (index k) = D.lower := by rw [hk, hlower]
    have hrec := recovery_corrected D hq a cutoff (fun i => basis.label (index i))
      k hkl raw (fun r l i => c r l (index i)) hold
    rw [correction_enumerated_active index hinj high low
      (fun i => D.weight (basis.label i)) hw k hk hhigh a c] at hrec
    exact hrec
  · have hhigh : high ∉ Finset.univ.image index := by
      rw [hactive]
      exact fun h => hlow (hjoint.mp h)
    have hlow' : low ∉ Finset.univ.image index := by rwa [hactive]
    rw [correction_enumerated_inactive index high low a c hlow']
    exact recovery_fixed D a cutoff (fun i => basis.label (index i))
      (weights_enumerated_inactive index high (fun i => D.weight (basis.label i)) hw hhigh)
      raw _ hold

theorem same_degree_joint (basis : OPE.FilteredBasis G) (high low : basis.Index)
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high)) (cutoff : ℕ) :
    high ∈ basis.active cutoff ↔ low ∈ basis.active cutoff := by
  rw [basis.active_iff, basis.active_iff, hd]

/-- For a downward correction only cutoffs strictly above the low degree
and no greater than the high degree can separate the selected labels. -/
theorem outside_window_joint (basis : OPE.FilteredBasis G) (high low : basis.Index)
    (hd : OPE.dimension (basis.label low) ≤ OPE.dimension (basis.label high))
    (cutoff : ℕ)
    (hout : cutoff ≤ OPE.dimension (basis.label low) ∨
      OPE.dimension (basis.label high) < cutoff) :
    high ∈ basis.active cutoff ↔ low ∈ basis.active cutoff := by
  rw [basis.active_iff, basis.active_iff]
  omega

/-- Exactly the all-cutoff outgoing recovery quantifier in generated data,
for a fixed input/test-paired raw vector and global coefficient table. -/
def CoherentRecovery (basis : OPE.FilteredBasis G) (e : ColorFrame B)
    (L : ℝ → InsertedFlowFamily G) (transport : SameTheoryWardTransportData e L)
    (lift : QuantumObservableLift G) (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (raw : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ) : Prop :=
  ∀ cutoff, ∃ n : ℕ, ∃ index : Fin n → basis.Index,
    Function.Injective index ∧ Finset.univ.image index = basis.active cutoff ∧
    QuantumPhysicalOutputRecovery e L transport lift W Q cutoff
      (fun i => basis.label (index i)) raw (fun r l i => c r l (index i))

theorem coherent_recovery_of_joint (basis : OPE.FilteredBasis G) (D : Direction G)
    (high low : basis.Index) (hne : high ≠ low)
    (hlower : D.lower = basis.label low)
    (hw : ∀ i, D.weight (basis.label i) = if i = high then 1 else 0)
    (hjoint : ∀ cutoff, high ∈ basis.active cutoff ↔ low ∈ basis.active cutoff)
    (a : ℝ) (raw : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ)
    (hold : CoherentRecovery basis e L transport lift W Q raw c) :
    CoherentRecovery basis e L transport (change lift D a) W Q raw
      (coordinateCorrection high low a c) := by
  intro cutoff
  obtain ⟨n, index, hinj, hactive, hrec⟩ := hold cutoff
  exact ⟨n, index, hinj, hactive,
    sector_recovery basis D high low hne hlower hw a cutoff index hinj hactive
      (hjoint cutoff) raw c hrec⟩

theorem coherent_recovery_same_degree (basis : OPE.FilteredBasis G) (D : Direction G)
    (high low : basis.Index) (hne : high ≠ low)
    (hlower : D.lower = basis.label low)
    (hw : ∀ i, D.weight (basis.label i) = if i = high then 1 else 0)
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : ℝ) (raw : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ)
    (hold : CoherentRecovery basis e L transport lift W Q raw c) :
    CoherentRecovery basis e L transport (change lift D a) W Q raw
      (coordinateCorrection high low a c) :=
  coherent_recovery_of_joint basis D high low hne hlower hw
    (same_degree_joint basis high low hd) a raw c hold

/-- The same global coefficient construction is reversible. This compares
the entire outgoing all-cutoff relation, not the rest of generated data. -/
theorem coherent_recovery_same_degree_iff (basis : OPE.FilteredBasis G) (D : Direction G)
    (high low : basis.Index) (hne : high ≠ low)
    (hlower : D.lower = basis.label low)
    (hw : ∀ i, D.weight (basis.label i) = if i = high then 1 else 0)
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : ℝ) (raw : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ) :
    CoherentRecovery basis e L transport (change lift D a) W Q raw
      (coordinateCorrection high low a c) ↔
    CoherentRecovery basis e L transport lift W Q raw c := by
  have hq : D.weight D.lower = 0 := by simp [hlower, hw, Ne.symm hne]
  constructor
  · intro h
    have hr := coherent_recovery_same_degree basis D high low hne hlower hw hd
      (-a) raw (coordinateCorrection high low a c) h
    simpa only [change_inverse D a hq, coordinateCorrection_inverse high low hne a c] using hr
  · exact coherent_recovery_same_degree basis D high low hne hlower hw hd a raw c

/-- The required direction is constructed, including the unit condition.
Positive degree, rather than strict lowering, excludes the unit coordinate. -/
def coordinateDirectionLE (basis : OPE.FilteredBasis G) (high low : basis.Index)
    (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) ≤ OPE.dimension (basis.label high)) : Direction G where
  lower := basis.label low
  weight := coordinateWeight basis high
  unit := by
    by_contra hn
    have hb := basis.classicalCoordinates_degree 1 high (Finsupp.mem_support_iff.mpr hn)
    change OPE.dimension (basis.label high) ≤ intrinsicEngineeringDimension 1 at hb
    rw [unit_dimension] at hb
    omega
  relations p q hr := congrArg (fun c : basis.Index →₀ ℝ => c high)
    (basis.classicalCoordinates_relations p q hr)
  filtered p hp := hd.trans
    (basis.classicalCoordinates_degree p high (Finsupp.mem_support_iff.mpr hp))

theorem directionLE_weights (basis : OPE.FilteredBasis G) (high low : basis.Index)
    (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) ≤ OPE.dimension (basis.label high))
    (i : basis.Index) :
    (coordinateDirectionLE basis high low hpos hd).weight (basis.label i) =
      if i = high then 1 else 0 := by
  simp [coordinateDirectionLE, coordinateWeight, coordinates_basis, Finsupp.single_apply]

theorem coherent_coordinate_change (basis : OPE.FilteredBasis G) (high low : basis.Index)
    (hne : high ≠ low) (hpos : 0 < OPE.dimension (basis.label high))
    (hd : OPE.dimension (basis.label low) = OPE.dimension (basis.label high))
    (a : ℝ) (raw : BigradedMonomialVector G) (c : ℕ → ℕ → basis.Index → ℂ)
    (hold : CoherentRecovery basis e L transport lift W Q raw c) :
    CoherentRecovery basis e L transport
      (change lift (coordinateDirectionLE basis high low hpos hd.le) a) W Q raw
      (coordinateCorrection high low a c) :=
  coherent_recovery_same_degree basis (coordinateDirectionLE basis high low hpos hd.le)
    high low hne rfl (directionLE_weights basis high low hpos hd.le) hd a raw c hold

#print axioms coordinateCorrection_graph
#print axioms coordinateCorrection_inverse
#print axioms weightedOn_coordinate
#print axioms correction_enumerated_active
#print axioms correction_enumerated_inactive
#print axioms weights_enumerated_inactive
#print axioms sector_recovery
#print axioms same_degree_joint
#print axioms outside_window_joint
#print axioms coherent_recovery_of_joint
#print axioms coherent_recovery_same_degree
#print axioms coherent_recovery_same_degree_iff
#print axioms coordinateDirectionLE
#print axioms directionLE_weights
#print axioms coherent_coordinate_change
end YMYMG.OutputRecoveryCoherent
