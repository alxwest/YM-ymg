import QuantumClosureShift
import YangMills.IntrinsicFiltration

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
A global elementary finite renormalization of the actual observable lift.
The correction is linear on ALL labels, respects identities on connections,
fixes the unit, and obeys the intrinsic filtration. The complete native
Compatible bundle is preserved; insertion-limit compatibility is separate.
-/
noncomputable section
open Filter
open scoped BigOperators
namespace YMYMG.DictionaryRenormalization
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.QuantumShift

variable {G : CompactSimpleGaugeGroup}

structure Direction (G : CompactSimpleGaugeGroup) where
  lower : InvariantInsertionLabel G
  weight : InvariantInsertionLabel G →ₗ[ℝ] ℝ
  unit : weight 1 = 0
  relations : ∀ (p q : InvariantInsertionLabel G), CurvatureJetPolynomial.sameOnConnections
    (p : CurvatureJetPolynomial G) (q : CurvatureJetPolynomial G) → weight p = weight q
  filtered : ∀ p, weight p ≠ 0 →
    intrinsicEngineeringDimension lower ≤ intrinsicEngineeringDimension p

def change (lift : QuantumObservableLift G) (D : Direction G) (a : ℝ) :
    QuantumObservableLift G where
  coefficient g p
    | 0, UV => lift.coefficient g p 0 UV
    | loop+1, UV => lift.coefficient g p (loop+1) UV +
        ((g : ℂ)^2 * (a * D.weight p : ℝ)) • lift.coefficient g D.lower loop UV
  physicalCoefficient g p := shifted lift g p D.lower (a * D.weight p : ℝ)

variable {B : InvariantForm G} {e : ColorFrame B}
  {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}
  {lift : QuantumObservableLift G}

theorem relations_preserved (h : lift.Compatible e anomaly Q)
    (D : Direction G) (a : ℝ) (p q : InvariantInsertionLabel G)
    (hr : CurvatureJetPolynomial.sameOnConnections
      (p : CurvatureJetPolynomial G) (q : CurvatureJetPolynomial G)) :
    SameQuantumLabelClass Q (change lift D a) p q := by
  obtain ⟨primitive, support, smooth, grading, equation⟩ := h.relations p q hr
  refine ⟨primitive, support, smooth, grading, ?_⟩
  intro g loop output ha hd
  have same := D.relations p q hr
  have diff : (change lift D a).physicalCoefficient g p loop output -
      (change lift D a).physicalCoefficient g q loop output =
      lift.physicalCoefficient g p loop output - lift.physicalCoefficient g q loop output := by
    cases loop <;> simp [change, shifted, Finsupp.add_apply, Finsupp.smul_apply, same]
  rw [diff]
  exact equation g loop output ha hd

theorem finite_grading (h : lift.Compatible e anomaly Q) (D : Direction G)
    (a g : ℝ) (p : InvariantInsertionLabel G) (loop : ℕ) (UV : ℝ)
    (m : LocalMonomial G) :
    (change lift D a).coefficient g p loop UV m = (g : ℂ)^(m.legs.length+2*loop) *
      (change lift D a).coefficient 1 p loop UV m := by
  cases loop with
  | zero => exact h.finite_graph_grading g p 0 UV m
  | succ loop =>
    simp only [change, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [h.finite_graph_grading g p (loop+1) UV m,
      h.finite_graph_grading g D.lower loop UV m]
    simp only [Complex.ofReal_one, one_pow, one_mul]
    rw [show m.legs.length+2*(loop+1) = (m.legs.length+2*loop)+2 by omega, pow_add]
    ring

theorem finite_support (h : lift.Compatible e anomaly Q) (D : Direction G)
    (a g : ℝ) (p : InvariantInsertionLabel G) (loop : ℕ) (UV : ℝ)
    (m : LocalMonomial G) (hUV : 0 < UV)
    (hn : (change lift D a).coefficient g p loop UV m ≠ 0) :
    m.Admissible ∧ m.dimension ≤ intrinsicEngineeringDimension p ∧
      m.ghostNumber = 0 ∧ m.parity = false := by
  cases loop with
  | zero => exact h.finite_support g p 0 UV m hUV hn
  | succ loop =>
    by_cases hp : lift.coefficient g p (loop+1) UV m ≠ 0
    · exact h.finite_support g p (loop+1) UV m hUV hp
    · have hw : D.weight p ≠ 0 := by
        intro hz
        apply hn
        simp [change, hz, not_ne_iff.mp hp]
      have hq : lift.coefficient g D.lower loop UV m ≠ 0 := by
        intro hz
        apply hn
        simp [change, Finsupp.add_apply, Finsupp.smul_apply, hz, not_ne_iff.mp hp]
      have hs := h.finite_support g D.lower loop UV m hUV hq
      exact ⟨hs.1, hs.2.1.trans (D.filtered p hw), hs.2.2⟩

/-- Every field of the original native Compatible structure is proved.
The old quantum primitives suffice: equal classical labels receive exactly
equal corrections, so their differences are unchanged. -/
theorem compatible (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ) :
    (change lift D a).Compatible e anomaly Q where
  same_ward_limit := h.same_ward_limit
  ward_filtered := h.ward_filtered
  relations := relations_preserved h D a
  ward_graph_grading := h.ward_graph_grading
  finite_graph_grading := finite_grading h D a
  physical_graph_grading g p loop m := shifted_graph_grading h g p D.lower _ loop m
  linear_add g p q loop UV := by
    cases loop with
    | zero => exact h.linear_add g p q 0 UV
    | succ loop =>
      simp only [change, h.linear_add, map_add, mul_add, Complex.ofReal_add, add_smul]
      abel
  linear_smul g c p loop UV := by
    cases loop with
    | zero => exact h.linear_smul g c p 0 UV
    | succ loop =>
      simp only [change, h.linear_smul, map_smul, smul_eq_mul, Complex.ofReal_mul,
        smul_add, smul_smul]
      congr 1
      congr 1
      ring
  unit_corrections g loop UV hl := by
    cases loop with
    | zero => omega
    | succ loop => simp [change, D.unit, h.unit_corrections g (loop+1) UV (by omega)]
  tree g p UV hUV := h.tree g p UV hUV
  finite_support := finite_support h D a
  physical_support g p loop m hn := by
    by_cases hw : D.weight p = 0
    · have he : (change lift D a).physicalCoefficient g p loop =
          lift.physicalCoefficient g p loop := by cases loop <;> simp [change, shifted, hw]
      exact h.physical_support g p loop m (by simpa only [he] using hn)
    · exact shifted_support h g p D.lower _ loop (D.filtered p hw) m hn
  coefficient_limit g p loop m := by
    cases loop with
    | zero => exact h.coefficient_limit g p 0 m
    | succ loop =>
      simpa only [change, shifted, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using
        (h.coefficient_limit g p (loop+1) m).add
          ((h.coefficient_limit g D.lower loop m).const_mul
            ((g : ℂ)^2 * (a * D.weight p : ℝ)))
  finite_coupling_smooth p loop UV m hUV := by
    cases loop with
    | zero => exact h.finite_coupling_smooth p 0 UV m hUV
    | succ loop =>
      simp only [change, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      have hp := h.finite_coupling_smooth p (loop+1) UV m hUV
      have hq := h.finite_coupling_smooth D.lower loop UV m hUV
      exact hp.add (((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul hq)
  physical_coupling_smooth p loop m := by
    cases loop with
    | zero => exact h.physical_coupling_smooth p 0 m
    | succ loop =>
      simp only [change, shifted, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      have hp := h.physical_coupling_smooth p (loop+1) m
      have hq := h.physical_coupling_smooth D.lower loop m
      exact hp.add (((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul hq)
  cocycle g p loop output ha _ := by
    change (∑ l : Fin (loop+1), (shifted lift g p D.lower _ l.val).sum
      (fun input c => c * Q.coefficient g (loop-l.val) input output)) = 0
    simpa only [wardMap_apply] using shifted_closed h g p D.lower
      (a * D.weight p : ℝ) loop output ha

theorem unit_dimension : intrinsicEngineeringDimension (1 : InvariantInsertionLabel G) = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply intrinsicEngineeringDimension_le_of_representative 1 1 0
  · intro A x; rfl
  · intro m hm
    change m ∈ (1 : CurvatureJetPolynomial G).support at hm
    simp only [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst m
    simp [CurvatureJetPolynomial.monomialDimension]

def coordinateWeight (basis : OPE.FilteredBasis G) (i : basis.Index) :
    InvariantInsertionLabel G →ₗ[ℝ] ℝ where
  toFun p := basis.classicalCoordinates p i
  map_add' p q := congrArg (fun c : basis.Index →₀ ℝ => c i)
    (basis.coordinatesLinearMap.map_add p q)
  map_smul' c p := congrArg (fun v : basis.Index →₀ ℝ => v i)
    (basis.coordinatesLinearMap.map_smul c p)

theorem coordinates_basis (basis : OPE.FilteredBasis G) (i : basis.Index) :
    basis.classicalCoordinates (basis.label i) = Finsupp.single i 1 := by
  apply basis.coefficients_unique
  intro A x
  rw [basis.classicalCoordinates_meaning]
  simp [OPE.FilteredBasis.evaluateCoefficients_apply]

/-- A strictly lower label and an actual basis coordinate supply every
Direction condition. No new rule identifying classical labels is assumed. -/
def coordinateDirection (basis : OPE.FilteredBasis G) (high : basis.Index)
    (low : InvariantInsertionLabel G)
    (hlt : intrinsicEngineeringDimension low < OPE.dimension (basis.label high)) :
    Direction G where
  lower := low
  weight := coordinateWeight basis high
  unit := by
    by_contra hn
    have hd := basis.classicalCoordinates_degree 1 high (Finsupp.mem_support_iff.mpr hn)
    change intrinsicEngineeringDimension (basis.label high) ≤ intrinsicEngineeringDimension 1 at hd
    rw [unit_dimension] at hd
    change intrinsicEngineeringDimension low < intrinsicEngineeringDimension (basis.label high) at hlt
    omega
  relations p q hr := congrArg (fun c : basis.Index →₀ ℝ => c high)
    (basis.classicalCoordinates_relations p q hr)
  filtered p hp := hlt.le.trans
    (basis.classicalCoordinates_degree p high (Finsupp.mem_support_iff.mpr hp))

theorem coordinate_weight_selected (basis : OPE.FilteredBasis G) (i : basis.Index) :
    coordinateWeight basis i (basis.label i) = 1 := by
  simp [coordinateWeight, coordinates_basis]

theorem coordinate_weight_lower (basis : OPE.FilteredBasis G) (high : basis.Index)
    (low : InvariantInsertionLabel G)
    (hlt : intrinsicEngineeringDimension low < OPE.dimension (basis.label high)) :
    coordinateWeight basis high low = 0 := by
  by_contra hn
  have hd := basis.classicalCoordinates_degree low high (Finsupp.mem_support_iff.mpr hn)
  exact (not_le_of_gt hlt) hd

/-- A genuinely higher-degree label has a nonzero coordinate above the
lower label's degree. Otherwise finite reconstruction would lower its
intrinsic degree, contradicting the assumed strict inequality. -/
theorem exists_higher_coordinate (basis : OPE.FilteredBasis G)
    (high low : InvariantInsertionLabel G)
    (hlt : intrinsicEngineeringDimension low < intrinsicEngineeringDimension high) :
    ∃ i, basis.classicalCoordinates high i ≠ 0 ∧
      intrinsicEngineeringDimension low < OPE.dimension (basis.label i) := by
  classical
  by_contra! hn
  have hd : intrinsicEngineeringDimension (basis.reconstructedLabel high) ≤
      intrinsicEngineeringDimension low := by
    unfold OPE.FilteredBasis.reconstructedLabel Finsupp.sum
    apply intrinsicEngineeringDimension_sum_le
    intro i hi
    apply intrinsicEngineeringDimension_smul_le
    exact hn i (Finsupp.mem_support_iff.mp hi)
  rw [basis.reconstructedLabel_dimension] at hd
  exact (not_le_of_gt hlt) hd

def scaleDirection (D : Direction G) (c : ℝ) : Direction G where
  lower := D.lower
  weight := c • D.weight
  unit := by simp [D.unit]
  relations p q hr := by simp [D.relations p q hr]
  filtered p hp := D.filtered p (by intro hz; apply hp; simp [hz])

/-- The desired correction extends to ALL labels even if the selected
observable is not one of the chosen basis labels. The direction is
nilpotent because its weight on its own lower output is zero. -/
theorem direction_for_pair (basis : OPE.FilteredBasis G)
    (high low : InvariantInsertionLabel G)
    (hlt : intrinsicEngineeringDimension low < intrinsicEngineeringDimension high) :
    ∃ D : Direction G, D.lower = low ∧ D.weight high = 1 ∧ D.weight D.lower = 0 := by
  classical
  obtain ⟨i, hi, hd⟩ := exists_higher_coordinate basis high low hlt
  let D := coordinateDirection basis i low hd
  refine ⟨scaleDirection D (basis.classicalCoordinates high i)⁻¹, rfl, ?_, ?_⟩
  · simp [scaleDirection, D, coordinateDirection, coordinateWeight, hi]
  · change (basis.classicalCoordinates high i)⁻¹ * coordinateWeight basis i low = 0
    rw [coordinate_weight_lower basis i low hd, mul_zero]

theorem change_fixed_finite (D : Direction G) (a g : ℝ) (p : InvariantInsertionLabel G)
    (hp : D.weight p = 0) (loop : ℕ) (UV : ℝ) :
    (change lift D a).coefficient g p loop UV = lift.coefficient g p loop UV := by
  cases loop <;> simp [change, hp]

theorem change_fixed_physical (D : Direction G) (a g : ℝ) (p : InvariantInsertionLabel G)
    (hp : D.weight p = 0) (loop : ℕ) :
    (change lift D a).physicalCoefficient g p loop = lift.physicalCoefficient g p loop := by
  cases loop <;> simp [change, shifted, hp]

theorem change_inverse (D : Direction G) (a : ℝ) (hq : D.weight D.lower = 0) :
    change (change lift D a) D (-a) = lift := by
  have hf : (change (change lift D a) D (-a)).coefficient = lift.coefficient := by
    funext g p loop UV
    cases loop with
    | zero => rfl
    | succ loop =>
      change lift.coefficient g p (loop+1) UV +
        ((g : ℂ)^2 * (a * D.weight p : ℝ)) • lift.coefficient g D.lower loop UV +
        ((g : ℂ)^2 * (-a * D.weight p : ℝ)) •
          (change lift D a).coefficient g D.lower loop UV = _
      rw [change_fixed_finite D a g D.lower hq]
      simp [neg_mul, mul_neg, neg_smul]
  have hp : (change (change lift D a) D (-a)).physicalCoefficient = lift.physicalCoefficient := by
    funext g p loop
    cases loop with
    | zero => rfl
    | succ loop =>
      change lift.physicalCoefficient g p (loop+1) +
        ((g : ℂ)^2 * (a * D.weight p : ℝ)) • lift.physicalCoefficient g D.lower loop +
        ((g : ℂ)^2 * (-a * D.weight p : ℝ)) •
          (change lift D a).physicalCoefficient g D.lower loop = _
      rw [change_fixed_physical D a g D.lower hq]
      simp [neg_mul, mul_neg, neg_smul]
  cases hchanged : change (change lift D a) D (-a)
  cases lift
  simp only [hchanged] at hf hp
  exact congrArg₂ QuantumObservableLift.mk hf hp

#print axioms relations_preserved
#print axioms finite_grading
#print axioms finite_support
#print axioms compatible
#print axioms unit_dimension
#print axioms coordinateWeight
#print axioms coordinates_basis
#print axioms coordinateDirection
#print axioms coordinate_weight_selected
#print axioms coordinate_weight_lower
#print axioms exists_higher_coordinate
#print axioms scaleDirection
#print axioms direction_for_pair
#print axioms change_fixed_finite
#print axioms change_fixed_physical
#print axioms change_inverse
end YMYMG.DictionaryRenormalization
