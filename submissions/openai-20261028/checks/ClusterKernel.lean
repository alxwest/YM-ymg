import ClusterCones
import SourceScalar

/-! Pointwise scalar clustering in all separation directions. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM YM.OS YM.Word YM.EveryPhase Filter Set
open scoped Topology NNReal InnerProductSpace BigOperators

def joinPoints {n m : ℕ} (x : Points n) (y : Points m) (b : E4) : Points (n+m) :=
  points (Fin.append x.ofLp (fun j => y j + b))

theorem realize_join {G : Gauge} {L : Register G} {n m : ℕ}
    (v : L.Token) (x : Points n) (y : Points m) (b : E4) :
    realize (fun _ : Fin (n+m) => v) (joinPoints x y b) =
      realize (fun _ : Fin n => v) x ++ carry (realize (fun _ : Fin m => v) y) b := by
  simp only [realize, carry, List.map_ofFn]
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [joinPoints]

theorem move_join {n m : ℕ} (R : Ortho) (x : Points n) (y : Points m) (b : E4) :
    Points.move R (joinPoints x y b) =
      joinPoints (Points.move R x) (Points.move R y) (Ortho.move R b) := by
  apply PiLp.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Points.move, joinPoints]
  · simpa [Points.move, joinPoints] using (Ortho.motion R).map_add (y j) b

theorem exists_signed_large_coordinate (b : E4) (R : ℝ) (hR : 0 ≤ R)
    (hb : R < ‖b.ofLp‖) : ∃ s : Signed, R < Ortho.move s.ortho b timeAxis := by
  have hk : ∃ k : Axis, R < ‖b k‖ := by
    by_contra hn
    push Not at hn
    exact hb.not_ge ((pi_norm_le_iff_of_nonneg hR).mpr hn)
  obtain ⟨k, hk⟩ := hk
  refine ⟨⟨Equiv.swap k timeAxis, fun _ => decide (b k < 0)⟩, ?_⟩
  rw [Signed.ortho_move]
  simp only [Signed.act, Equiv.symm_swap, Equiv.swap_apply_right]
  by_cases h : b k < 0
  · simpa [h, Real.norm_eq_abs, abs_of_neg h] using hk
  · simpa [h, Real.norm_eq_abs, abs_of_nonneg (le_of_not_gt h)] using hk

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

theorem scalarKernel_cone_cluster {n m : ℕ} (x : Points n) (y : Points m)
    (hx : x ∈ conf n) (hy : y ∈ conf m) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ b : E4, R ≤ b timeAxis →
      ‖scalarKernel F (n+m) (joinPoints x y b) -
        scalarKernel F n x * scalarKernel F m y‖ < ε := by
  obtain ⟨A⟩ := almanac F
  let v : C.book.Token := ⟨4, S.representative 4 (Trace.traceField F)⟩
  have h := chamber_word_cone_cluster (A.chambers F.α.atPoint)
    (F.phase.phase.states F.α.atPoint) (every A F.α.atPoint)
    (realize (fun _ => v) x) (realize (fun _ => v) y)
    ((realized _ _).mpr hx) ((realized _ _).mpr hy) ε hε
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun b hb => ?_⟩
  have he := hR b hb
  rw [← realize_join, Table.readAt, Table.readAt, Table.readAt] at he
  exact he

/-- No rate is asserted. The threshold is uniform over all directions of b. -/
theorem scalarKernel_radial_cluster {n m : ℕ} (x : Points n) (y : Points m)
    (hx : x ∈ conf n) (hy : y ∈ conf m) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : E4, R < ‖b.ofLp‖ →
      joinPoints x y b ∈ conf (n+m) →
      ‖scalarKernel F (n+m) (joinPoints x y b) -
        scalarKernel F n x * scalarKernel F m y‖ < ε := by
  classical
  have hc (s : Signed) := scalarKernel_cone_cluster F
    (Points.move s.ortho x) (Points.move s.ortho y)
    (Points.move_in s.ortho hx) (Points.move_in s.ortho hy) ε hε
  choose R hR using hc
  let T := ∑ s : Signed, max (R s) 0
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hTR (s : Signed) : R s ≤ T := (le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ s))
  refine ⟨T, hT, fun b hb hxy => ?_⟩
  obtain ⟨s, hs⟩ := exists_signed_large_coordinate b T hT hb
  have hh := hR s (Ortho.move s.ortho b) ((hTR s).trans hs.le)
  rw [← move_join, scalarKernel_rotation F _ hxy,
    scalarKernel_rotation F _ hx, scalarKernel_rotation F _ hy] at hh
  exact hh

#print axioms scalarKernel_cone_cluster
#print axioms scalarKernel_radial_cluster
end YMOSBridge
