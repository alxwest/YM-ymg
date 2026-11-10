import ClusterSchwartz
import RemainingObligations

/-! Full target E4 and the unconditional OS record for the same selected,
centered stress-trace hierarchy. No uniqueness of the unselected IR limit is claimed. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM Filter Set
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

theorem E4_cluster_norm (n m : ℕ) (f : ZeroDiagonalSchwartz 3 n)
    (g : ZeroDiagonalSchwartz 3 m) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ a : SpacetimeDim 3, R < ‖a‖ →
      ∀ g_a : ZeroDiagonalSchwartz 3 m,
        (∀ x, g_a.1 x = g.1 (fun i => x i-a)) →
        ∀ fg_a : ZeroDiagonalSchwartz 3 (n+m),
          (∀ x, fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
          ‖schwinger F (n+m) fg_a - schwinger F n f * schwinger F m g‖ < ε := by
  classical
  by_contra hn
  push Not at hn
  choose a ha g_a hg fg_a hfg hbad using fun k : ℕ => hn (k : ℝ)
  have ht : Tendsto (fun k => ‖a k‖) atTop atTop :=
    tendsto_atTop_mono (fun k => (ha k).le) tendsto_natCast_atTop_atTop
  have hc := schwinger_cluster_sequence F f g a ht g_a hg fg_a hfg
  have hz : Tendsto (fun k => ‖schwinger F (n+m) (fg_a k) -
      schwinger F n f * schwinger F m g‖) atTop (𝓝 0) := by
    simpa using (hc.sub (tendsto_const_nhds
      (x := schwinger F n f * schwinger F m g))).norm
  obtain ⟨k, hk⟩ := (hz.eventually (gt_mem_nhds hε)).exists
  exact (hbad k).not_gt hk

/-- The exact spatial E4 field from the vendored OSreconstruction definition. -/
theorem E4_cluster : ClusterObligation F := by
  intro n m f g ε hε
  obtain ⟨R, hR⟩ := E4_cluster_norm F n m f g ε hε
  let T := max R 0 + 1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨2*T, by positivity, fun a _ ha => hR a ?_⟩
  have hs : (∑ i : Fin 3, (a (Fin.succ i))^2) ≤ 3 * ‖a‖^2 := by
    calc
      _ ≤ ∑ _ : Fin 3, ‖a‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := norm_le_pi_norm a (Fin.succ i)
        have hi' : |a (Fin.succ i)| ≤ ‖a‖ := hi
        nlinarith [sq_abs (a (Fin.succ i)), norm_nonneg a,
          abs_nonneg (a (Fin.succ i))]
      _ = _ := by simp
  by_contra hn
  have hr : ‖a‖ ≤ R := le_of_not_gt hn
  have hrt : R < T := by dsimp [T]; linarith [le_max_left R 0]
  nlinarith [norm_nonneg a]

/-- E0, E1, E2, E3 and E4 for the original selected hierarchy, without any
additional analytic premise. -/
def verifiedOS : OsterwalderSchraderAxioms 3 := completeOS F (E4_cluster F)

theorem verifiedOS_growth : Nonempty (OSArityLinearGrowthCondition 3 (verifiedOS F)) :=
  E0_prime F (E4_cluster F)

/-- Actual outputs of the submitted construction satisfy all target OS axioms
and the corrected E0-prime growth condition, retaining the original limit orders. -/
theorem constructed_OS_family
    {G : Gauge} (hG : G.Simple) {b : ℝ} (hb : 0 < b) (p : Extraction.Order) :
    let C := (Independent.fundedRun hG hb).family
    ∃ (q : Extraction.Order) (S : Table C.book) (F : Spec.Final C (p.refine q) S),
      (Extraction.Order.mk Extraction.Sequence.full (p.refine q).per).Ordered C S ∧
      ClusterObligation F ∧
      Nonempty (OSArityLinearGrowthCondition 3 (verifiedOS F)) := by
  obtain ⟨q, S, F, ho, _, _⟩ := constructed_tempered_family hG hb p
  exact ⟨q, S, F, ho, E4_cluster F, verifiedOS_growth F⟩

#print axioms E4_cluster_norm
#print axioms E4_cluster
#print axioms verifiedOS
#print axioms verifiedOS_growth
#print axioms constructed_OS_family
end YMOSBridge
