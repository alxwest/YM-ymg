import ClusterCore
import YM.Ground.Lean

/-! Clustering uniform over all transverse translations, in a fixed axis cone. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM YM.OS YM.Word YM.Table Filter Set
open scoped Topology NNReal InnerProductSpace
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis}

theorem chamber_vacuum_transverse (V : Chamber S a) (b : Cross a) :
    V.flow.U b V.omega = V.omega := by
  change V.flow.U b (V.GNS.plant (air a)) = V.GNS.plant (air a)
  rw [← V.across]
  congr 1

theorem chamber_transverse_cluster (V : Chamber S a) (hS : S.Basic)
    (hV : V.UniqueHeat) (x y : V.H) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ≥0, ∀ t ≥ T, ∀ b : Cross a,
      ‖inner ℂ x (V.flow.U b (V.flow.E t y)) -
        inner ℂ x V.omega * inner ℂ V.omega y‖ < ε := by
  have ht : Tendsto (fun t : ℝ≥0 => ‖x‖ * ‖V.flow.E t y - V.flow.orth y‖)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (((V.flow.emerges y).sub (tendsto_const_nhds (x := V.flow.orth y))).norm)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨T, fun t ht b => lt_of_le_of_lt ?_ (hT t ht)⟩
  have hp : V.flow.U b (V.flow.orth y) = V.flow.orth y := by
    rw [chamber_ground_projection V hS hV, map_smul, chamber_vacuum_transverse]
  have hi : inner ℂ x (V.flow.orth y) =
      inner ℂ x V.omega * inner ℂ V.omega y := by
    rw [chamber_ground_projection V hS hV, inner_smul_right, mul_comm]
  rw [← hi, ← hp, ← inner_sub_right, ← map_sub]
  exact (norm_inner_le_norm x _).trans_eq (by rw [V.flow.unitary, hp])

/-- Arbitrary separated words have positive-half-space representatives whose
vacuum matrix elements retain the original one-word expectations. -/
theorem chamber_word_placements (V : Chamber S a) (H : S.Hierarchy)
    (p q : L.Word) (hp : distinct p) (hq : distinct q) :
    ∃ (r s : ℝ) (v w : Future L a),
      inner ℂ (V.GNS.plant v) V.omega = S.expect p ∧
      inner ℂ V.omega (V.GNS.plant w) = S.expect q ∧
      ∀ x : E4, r+s ≤ x a →
        S.expect (p ++ carry q x) =
          inner ℂ (V.GNS.plant v) (V.flow.U (Semigroup.SEP a x)
            (V.flow.E (x a-r-s).toNNReal (V.GNS.plant w))) := by
  obtain ⟨r, hv⟩ := Ground.released (reflect p a) (reflects a hp) (a := a)
  obtain ⟨s, hw⟩ := Ground.released q hq (a := a)
  let v : Future L a := ⟨_, hv⟩
  let w : Future L a := ⟨_, hw⟩
  refine ⟨r, s, v, w, ?_, ?_, ?_⟩
  · change inner ℂ (V.GNS.plant v) (V.GNS.plant (air a)) = _
    rw [V.GNS.measure]
    simp only [Table.gram, air, List.append_nil]
    change S.expect (reflect (carry (reflect p a) (r • basis a)) a) = _
    rw [refl_over, OS.reflect_twice]
    exact invariance H.translations hp _
  · change inner ℂ (V.GNS.plant (air a)) (V.GNS.plant w) = _
    rw [V.GNS.measure]
    change S.expect ([] ++ carry q (s • basis a)) = _
    simpa only [List.nil_append] using invariance H.translations hq (s • basis a)
  · intro x hx
    let b := Semigroup.SEP a x
    let t := (x a-r-s).toNNReal
    have hdist := twoSides v.property (over (travel w t) b).property
    have hy : (over (travel w t) b).val =
        carry w.val (b.val + (t : ℝ) • basis a) := by
      simp [over, travel, add_comm]
    have he : carry (reflect v.val a ++ carry w.val (b.val + (t : ℝ) • basis a))
        (r • basis a) = p ++ carry q x := by
      dsimp only [v, w]
      rw [refl_over, OS.reflect_twice, distribute, paths, paths, paths,
        show Ortho.move (Signed.reflect a) (r • basis a) = -(r • basis a) by
          ext i; by_cases h : i = a <;> simp [h, Signed.mirrored], neg_add_cancel, rest]
      congr 2
      change _ + (((x - x a • basis a) + (t : ℝ) • _) + _) = x
      dsimp only [t]
      rw [Real.coe_toNNReal _ (by linarith)]
      module
    rw [Ground.going V H, ← he]
    exact invariance H.translations (hy ▸ hdist) _

theorem chamber_word_cone_cluster (V : Chamber S a) (H : S.Hierarchy)
    (hV : V.UniqueHeat) (p q : L.Word) (hp : distinct p) (hq : distinct q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ b : E4, R ≤ b a →
      ‖S.expect (p ++ carry q b) - S.expect p * S.expect q‖ < ε := by
  obtain ⟨r, s, v, w, hv, hw, he⟩ := chamber_word_placements V H p q hp hq
  obtain ⟨T, hT⟩ := chamber_transverse_cluster V H.laws hV
    (V.GNS.plant v) (V.GNS.plant w) ε hε
  refine ⟨r+s+T, fun b hb => ?_⟩
  have hnonneg : 0 ≤ b a-r-s := by linarith [T.coe_nonneg]
  rw [he b (by linarith [T.coe_nonneg])]
  rw [← hv, ← hw]
  apply hT
  exact_mod_cast (show (T : ℝ) ≤ ((b a-r-s).toNNReal : ℝ) by
    rw [Real.coe_toNNReal _ hnonneg]; linarith)

#print axioms chamber_vacuum_transverse
#print axioms chamber_transverse_cluster
#print axioms chamber_word_placements
#print axioms chamber_word_cone_cluster
end YMOSBridge
