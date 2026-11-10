import YM.EveryPhase.Extension

/-! Consequences of the submitted unique heat vacuum for clustering.
These are axis-separated word and Hilbert-space statements. They do not
yet discharge the target spatial, joint-Schwartz `ClusterObligation`. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM YM.OS YM.Word YM.EveryPhase Filter
open scoped Topology NNReal InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis}

/-- Uniqueness of the heat vacuum identifies the full ground projection. -/
theorem chamber_ground_projection (V : Chamber S a) (hS : S.Basic)
    (hV : V.UniqueHeat) (y : V.H) :
    V.flow.orth y = inner ℂ V.omega y • V.omega := by
  obtain ⟨z, hz⟩ := hV (V.D.orthogonalProjectionOnto y)
  have hz' : z • V.omega = V.flow.orth y := congrArg Subtype.val hz
  have hi : inner ℂ V.omega (V.flow.orth y) = inner ℂ V.omega y :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left V.omega0 y
  have hn : ‖V.omega‖ = 1 := nil_norm V.GNS hS
  rw [← hz', inner_smul_right, inner_self_eq_norm_sq_to_K, hn] at hi
  have he : z = inner ℂ V.omega y := by simpa using hi
  rw [← hz', he]

/-- Mixed heat pairings factorize, with no compact-support or rate premise. -/
theorem chamber_mixed_heat_limit (V : Chamber S a) (hS : S.Basic)
    (hV : V.UniqueHeat) (x y : V.H) :
    Tendsto (fun t : ℝ≥0 => inner ℂ x (V.flow.E t y)) atTop
      (𝓝 (inner ℂ x V.omega * inner ℂ V.omega y)) := by
  have h := tendsto_const_nhds.inner (V.flow.emerges y) (𝕜 := ℂ) (x := x)
  rw [chamber_ground_projection V hS hV, inner_smul_right, mul_comm] at h
  exact h

/-- A reflected word and a positive word factorize along the chamber axis.
Both words may have arbitrary registered labels and any finite length. -/
theorem chamber_word_cluster (V : Chamber S a) (hS : S.Basic)
    (hV : V.UniqueHeat) (u v : Future L a) :
    Tendsto (fun t : ℝ≥0 => S.gram a u.val (travel v t).val) atTop
      (𝓝 (S.expect (reflect u.val a) * S.expect v.val)) := by
  have h := chamber_mixed_heat_limit V hS hV (V.GNS.plant u) (V.GNS.plant v)
  simp_rw [← V.atBirth, V.GNS.measure] at h
  simpa [Chamber.omega, V.GNS.measure, Table.gram, air, reflect, act, conjugate] using h

variable {C : Family G} {o : Extraction.Order} {T : Table C.book}
    {F : Spec.Final C o T}

/-- Axis-separated word clustering is available in every constructed character. -/
theorem phase_word_cluster (A : Almanac F) (i : F.α.space.X)
    (u v : Future C.book timeAxis) :
    Tendsto (fun t : ℝ≥0 => (F.α.ensemble i).gram timeAxis u.val (travel v t).val)
      atTop (𝓝 ((F.α.ensemble i).expect (reflect u.val timeAxis) *
        (F.α.ensemble i).expect v.val)) :=
  chamber_word_cluster (A.chambers i) (F.phase.phase.states i).laws (every A i) u v

/-- The boundary Hilbert-space version, using its actual energy evolution. -/
theorem phase_mixed_heat_limit (A : Almanac F) (i : F.α.space.X)
    (x y : (A.actors i).operators.H) :
    Tendsto (fun t : ℝ≥0 => inner ℂ x (bHeat (A.J i) t y)) atTop
      (𝓝 (inner ℂ x (A.actors i).operators.vacuum *
        inner ℂ (A.actors i).operators.vacuum y)) := by
  have h := tendsto_const_nhds.inner (bHeat_limit (A.links i) (A.cores i) y)
    (𝕜 := ℂ) (x := x)
  rw [all_plant, inner_smul_right, mul_comm] at h
  exact h

#print axioms chamber_ground_projection
#print axioms chamber_mixed_heat_limit
#print axioms chamber_word_cluster
#print axioms phase_word_cluster
#print axioms phase_mixed_heat_limit
end YMOSBridge
