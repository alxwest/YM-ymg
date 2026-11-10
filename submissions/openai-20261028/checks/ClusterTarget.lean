import ClusterKernel
import TargetKernel

/-! Clustering expressed in the target coordinates, for every escaping sequence. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM Filter Set
open scoped Topology BigOperators

def blockShift (n m : ℕ) (a : SpacetimeDim 3) : NPointDomain 3 (n+m) :=
  Fin.append (fun _ => 0) (fun _ => a)

def joinConfig {n m : ℕ} (x : NPointDomain 3 n) (y : NPointDomain 3 m)
    (a : SpacetimeDim 3) : NPointDomain 3 (n+m) :=
  Fin.append x (fun j => y j+a)

theorem joinConfig_eq_add {n m : ℕ} (x : NPointDomain 3 n) (y : NPointDomain 3 m)
    (a : SpacetimeDim 3) : joinConfig x y a = Fin.append x y + blockShift n m a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [joinConfig, blockShift]

theorem configEquiv_join {n m : ℕ} (x : NPointDomain 3 n) (y : NPointDomain 3 m)
    (a : SpacetimeDim 3) : configEquiv (n+m) (joinConfig x y a) =
      joinPoints (configEquiv n x) (configEquiv m y) (pointEquiv a) := by
  apply PiLp.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [joinConfig, joinPoints, map_add]

theorem pointEquiv_supnorm (a : SpacetimeDim 3) : ‖(pointEquiv a).ofLp‖ = ‖a‖ := by
  simpa [cubedist, dist_eq_norm] using pointEquiv_cube a 0

theorem joinConfig_injective {n m : ℕ} (x : NPointDomain 3 n) (y : NPointDomain 3 m)
    (hx : Function.Injective x) (hy : Function.Injective y) (a : SpacetimeDim 3)
    (ha : ‖x‖+‖y‖ < ‖a‖) : Function.Injective (joinConfig x y a) := by
  have hcross (i : Fin n) (j : Fin m) : x i ≠ y j+a := by
    intro he
    have he' : a = x i-y j := by rw [he]; abel
    have hh : ‖a‖ ≤ ‖x‖+‖y‖ := by
      rw [he']
      exact (norm_sub_le _ _).trans (add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm y j))
    exact ha.not_ge hh
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [joinConfig, Fin.append_left]
    intro he
    exact congrArg (Fin.castAdd m) (hx he)
  · simp only [joinConfig, Fin.append_left, Fin.append_right]
    intro he
    exact (hcross i j he).elim
  · simp only [joinConfig, Fin.append_left, Fin.append_right]
    intro he
    exact (hcross j i he.symm).elim
  · simp only [joinConfig, Fin.append_right]
    intro he
    exact congrArg (Fin.natAdd n) (hy (add_right_cancel he))

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

theorem targetKernel_radial_cluster {n m : ℕ} (x : NPointDomain 3 n)
    (y : NPointDomain 3 m) (hx : Function.Injective x) (hy : Function.Injective y)
    (ε : ℝ) (hε : 0 < ε) : ∃ R : ℝ, ∀ a : SpacetimeDim 3, R < ‖a‖ →
      ‖(targetKernel F (n+m) (joinConfig x y a) : ℂ) -
        (targetKernel F n x : ℂ) * (targetKernel F m y : ℂ)‖ < ε := by
  obtain ⟨R, _, hR⟩ := scalarKernel_radial_cluster F (configEquiv n x) (configEquiv m y)
    ((configEquiv_conf x).mpr hx) ((configEquiv_conf y).mpr hy) ε hε
  refine ⟨max R (‖x‖+‖y‖), fun a ha => ?_⟩
  have hc := joinConfig_injective x y hx hy a ((le_max_right _ _).trans_lt ha)
  rw [targetKernel_eq F _ hc, targetKernel_eq F _ hx, targetKernel_eq F _ hy, configEquiv_join]
  apply hR
  · rw [pointEquiv_supnorm]
    exact (le_max_left _ _).trans_lt ha
  · rw [← configEquiv_join]
    exact (configEquiv_conf _).mpr hc

theorem targetKernel_cluster_tendsto {n m : ℕ} (x : NPointDomain 3 n)
    (y : NPointDomain 3 m) (hx : Function.Injective x) (hy : Function.Injective y)
    (a : ℕ → SpacetimeDim 3) (ha : Tendsto (fun k => ‖a k‖) atTop atTop) :
    Tendsto (fun k => (targetKernel F (n+m) (joinConfig x y (a k)) : ℂ)) atTop
      (𝓝 ((targetKernel F n x : ℂ) * (targetKernel F m y : ℂ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := targetKernel_radial_cluster F x y hx hy ε hε
  filter_upwards [ha.eventually (eventually_gt_atTop R)] with k hk
  simpa only [dist_eq_norm] using hR (a k) hk

#print axioms targetKernel_radial_cluster
#print axioms targetKernel_cluster_tendsto
end YMOSBridge
