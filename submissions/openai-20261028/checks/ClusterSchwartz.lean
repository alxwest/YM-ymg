import ClusterTarget
import ClusterDomination
import ImportedSchwartzProduct

/-! Dominated convergence for the exact joint flat Schwartz tests. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory Filter Set
open scoped Topology BigOperators

theorem zeroDiagonal_zero_of_noninjective {n : ℕ} (f : ZeroDiagonalSchwartz 3 n)
    (x : NPointDomain 3 n) (hx : ¬Function.Injective x) : f.1 x = 0 := by
  have hc : x ∈ CoincidenceLocus 3 n := by
    simp only [Function.Injective] at hx
    push Not at hx
    obtain ⟨i,j,he,hn⟩ := hx
    exact ⟨i,j,hn,he⟩
  apply norm_eq_zero.mp
  have h := congrArg norm (f.2 0 x hc)
  simpa only [norm_iteratedFDeriv_zero, norm_zero] using h

theorem joint_test_shift {n m : ℕ} (f : ZeroDiagonalSchwartz 3 n)
    (g g_a : ZeroDiagonalSchwartz 3 m) (fg_a : ZeroDiagonalSchwartz 3 (n+m))
    (a : SpacetimeDim 3) (hg : ∀ x, g_a.1 x = g.1 (fun i => x i-a))
    (hfg : ∀ x, fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x))
    (x : NPointDomain 3 (n+m)) :
    f.1.tensorProduct g.1 x = fg_a.1 (x + blockShift n m a) := by
  rw [hfg, hg, SchwartzMap.tensorProduct_apply]
  congr 1
  · congr 1
    funext i
    simp [splitFirst, blockShift]
  · congr 1
    funext i
    simp [splitLast, blockShift]

theorem split_measurePreserving (n m : ℕ) :
    MeasurePreserving (EuclideanField.appendDomainEquiv (SpacetimeDim 3) n m) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => SpacetimeDim 3) finSumFinEquiv
  exact (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin m => SpacetimeDim 3)).comp
    ((volume_measurePreserving_piCongrLeft
      (fun _ : Fin (n+m) => SpacetimeDim 3) finSumFinEquiv).symm e)

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

theorem cluster_integral_product {n m : ℕ} (f : ZeroDiagonalSchwartz 3 n)
    (g : ZeroDiagonalSchwartz 3 m) :
    (∫ x : NPointDomain 3 (n+m),
      ((targetKernel F n (splitFirst n m x) : ℂ) *
        (targetKernel F m (splitLast n m x) : ℂ)) * f.1.tensorProduct g.1 x) =
      schwinger F n f * schwinger F m g := by
  let e := EuclideanField.appendDomainEquiv (SpacetimeDim 3) n m
  let h := fun z : NPointDomain 3 n × NPointDomain 3 m =>
    ((targetKernel F n z.1 : ℂ) * f.1 z.1) * ((targetKernel F m z.2 : ℂ) * g.1 z.2)
  calc
    _ = ∫ x : NPointDomain 3 (n+m), h (e x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change ((targetKernel F n (splitFirst n m x) : ℂ) *
        (targetKernel F m (splitLast n m x) : ℂ)) *
          (f.1 (splitFirst n m x) * g.1 (splitLast n m x)) =
        ((targetKernel F n (splitFirst n m x) : ℂ) * f.1 (splitFirst n m x)) *
          ((targetKernel F m (splitLast n m x) : ℂ) * g.1 (splitLast n m x))
      ring
    _ = ∫ z, h z := (split_measurePreserving n m).integral_comp
      e.toHomeomorph.measurableEmbedding h
    _ = _ := integral_prod_mul (μ := volume) (ν := volume)
      (fun x => (targetKernel F n x : ℂ) * f.1 x)
      (fun y => (targetKernel F m y : ℂ) * g.1 y)

theorem weighted_kernel_cluster {n m : ℕ} (f : ZeroDiagonalSchwartz 3 n)
    (g : ZeroDiagonalSchwartz 3 m) (a : ℕ → SpacetimeDim 3)
    (ha : Tendsto (fun k => ‖a k‖) atTop atTop) (x : NPointDomain 3 (n+m)) :
    Tendsto (fun k => (targetKernel F (n+m) (x + blockShift n m (a k)) : ℂ) *
      f.1.tensorProduct g.1 x) atTop
      (𝓝 (((targetKernel F n (splitFirst n m x) : ℂ) *
        (targetKernel F m (splitLast n m x) : ℂ)) * f.1.tensorProduct g.1 x)) := by
  by_cases hx : Function.Injective (splitFirst n m x)
  · by_cases hy : Function.Injective (splitLast n m x)
    · have he (a : SpacetimeDim 3) : x + blockShift n m a =
          joinConfig (splitFirst n m x) (splitLast n m x) a := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          simp [blockShift, joinConfig, splitFirst, splitLast]
      simp_rw [he]
      exact (targetKernel_cluster_tendsto F _ _ hx hy a ha).mul tendsto_const_nhds
    · have hz : f.1.tensorProduct g.1 x = 0 := by
        rw [SchwartzMap.tensorProduct_apply, zeroDiagonal_zero_of_noninjective g _ hy, mul_zero]
      simp only [hz, mul_zero]
      exact tendsto_const_nhds
  · have hz : f.1.tensorProduct g.1 x = 0 := by
      rw [SchwartzMap.tensorProduct_apply, zeroDiagonal_zero_of_noninjective f _ hx, zero_mul]
    simp only [hz, mul_zero]
    exact tendsto_const_nhds

/-- Every escaping sequence of admissible translated products has the same
factorized limit. The product witnesses may vary with the sequence index. -/
theorem schwinger_cluster_sequence {n m : ℕ} (f : ZeroDiagonalSchwartz 3 n)
    (g : ZeroDiagonalSchwartz 3 m) (a : ℕ → SpacetimeDim 3)
    (ha : Tendsto (fun k => ‖a k‖) atTop atTop)
    (g_a : ℕ → ZeroDiagonalSchwartz 3 m)
    (hg : ∀ k x, (g_a k).1 x = g.1 (fun i => x i-a k))
    (fg_a : ℕ → ZeroDiagonalSchwartz 3 (n+m))
    (hfg : ∀ k x, (fg_a k).1 x = f.1 (splitFirst n m x) * (g_a k).1 (splitLast n m x)) :
    Tendsto (fun k => schwinger F (n+m) (fg_a k)) atTop
      (𝓝 (schwinger F n f * schwinger F m g)) := by
  let q := f.1.tensorProduct g.1
  let b k := blockShift n m (a k)
  obtain ⟨D, _, hD, hbound⟩ := translated_kernel_majorant F (n+m) q
  have he (k) (x) : q x = (fg_a k).1 (x+b k) :=
    joint_test_shift f g (g_a k) (fg_a k) (a k) (hg k) (hfg k) x
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun x : NPointDomain 3 (n+m) =>
      (targetKernel F (n+m) (x+b k) : ℂ) * q x) :=
    ((Complex.measurable_ofReal.comp ((targetKernel_measurable F (n+m)).comp
      (continuous_id.add continuous_const).measurable)).mul q.continuous.measurable).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence
    (fun x : NPointDomain 3 (n+m) => D * ∏ i, EuclideanField.centerWeight 5 (x i))
    hmeas hD (fun k => Eventually.of_forall (hbound (b k) (fg_a k) (he k)))
    (Eventually.of_forall (weighted_kernel_cluster F f g a ha))
  have hi (k) : (∫ x : NPointDomain 3 (n+m),
      (targetKernel F (n+m) (x+b k) : ℂ) * q x) = schwinger F (n+m) (fg_a k) := by
    simp_rw [he k]
    exact integral_add_right_eq_self
      (fun x => (targetKernel F (n+m) x : ℂ) * (fg_a k).1 x) (b k)
  simp_rw [hi, cluster_integral_product F f g] at hlim
  exact hlim

#print axioms cluster_integral_product
#print axioms weighted_kernel_cluster
#print axioms schwinger_cluster_sequence
end YMOSBridge
