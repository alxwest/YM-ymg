import YangMills.OSRecon.CoordinateTransport
import YangMills.Analysis.SchwartzSupportedDensity
import YangMills.Analysis.SchwartzExternalProduct

noncomputable section
open Filter Set SchwartzMap
open scoped Topology

namespace SchwartzMap

/-- Compact approximation that retains the original topological support. -/
theorem exists_compactCutoff_sequence_tsupport_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap E F) :
    ∃ g : ℕ → SchwartzMap E F,
      (∀ j, HasCompactSupport (g j : E → F) ∧ tsupport (g j) ⊆ tsupport f) ∧
      Tendsto g atTop (𝓝 f) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let χ : SchwartzMap E ℝ := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ : ∀ x, ‖x‖ ≤ 1 → χ x = 1 := by
    intro x hx
    exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, b] using hx)
  refine ⟨fun j => smulLeftCLM F (fun x => χ (((j : ℝ) + 1)⁻¹ • x)) f, ?_, ?_⟩
  · intro j
    refine ⟨hasCompactSupport_dilateCutoff χ b.hasCompactSupport f (by positivity), ?_⟩
    have hg : Function.HasTemperateGrowth (fun x : E => χ (((j : ℝ) + 1)⁻¹ • x)) :=
      χ.hasTemperateGrowth.comp
        (((j : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E).hasTemperateGrowth
    rw [smulLeftCLM_apply hg]
    exact tsupport_smul_subset_right _ _
  · exact (tendsto_smulLeftCLM_dilate χ hχ f).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end SchwartzMap

namespace YangMills.OSRecon

theorem exists_compact_ordered_sequence {n : ℕ} (h : SchwartzNPoint 3 n)
    (hh : tsupport h ⊆ OrderedPositiveTimeRegion 3 n) :
    ∃ g : ℕ → SchwartzNPoint 3 n,
      (∀ j, HasCompactSupport (g j) ∧
        tsupport (g j) ⊆ OrderedPositiveTimeRegion 3 n ∧
        VanishesToInfiniteOrderOnCoincidence (g j)) ∧
      Tendsto g atTop (𝓝 h) := by
  obtain ⟨g, hg, hlim⟩ := SchwartzMap.exists_compactCutoff_sequence_tsupport_subset h
  refine ⟨g, fun j => ?_, hlim⟩
  have hgj := (hg j).2.trans hh
  exact ⟨(hg j).1, hgj,
    VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion _ hgj⟩

theorem continuous_source_tensorProduct (n m : ℕ) :
    Continuous (fun fg : SchwartzNPoint 3 n × SchwartzNPoint 3 m =>
      fg.1.tensorProduct fg.2) := by
  have hc := (SchwartzMap.complexDomCongr
    (EuclideanField.appendDomainEquiv (SpacetimeDim 3) n m)).continuous.comp
      (SchwartzMap.continuous_externalProduct
        (E := NPointDomain 3 n) (F := NPointDomain 3 m))
  convert hc using 1
  ext fg x
  rfl

theorem continuous_source_osConj (n : ℕ) :
    Continuous (SchwartzNPoint.osConj : SchwartzNPoint 3 n → SchwartzNPoint 3 n) := by
  let θ : NPointDomain 3 n ≃L[ℝ] NPointDomain 3 n :=
    { toFun := timeReflectionN 3
      invFun := timeReflectionN 3
      left_inv := fun x => funext fun i => timeReflection_timeReflection 3 (x i)
      right_inv := fun x => funext fun i => timeReflection_timeReflection 3 (x i)
      map_add' := by
        intro x y
        funext i j
        simp only [timeReflectionN, timeReflection, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := by
        intro c x
        funext i j
        simp only [timeReflectionN, timeReflection, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        split_ifs <;> ring
      continuous_toFun := continuous_timeReflectionN 3
      continuous_invFun := continuous_timeReflectionN 3 }
  have hc := (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap).continuous.comp
    (SchwartzMap.complexDomCongr θ).continuous
  convert hc using 1
  ext f x
  rfl

theorem continuous_source_osConjTensorProduct (n m : ℕ) :
    Continuous (fun fg : SchwartzNPoint 3 n × SchwartzNPoint 3 m =>
      fg.1.osConjTensorProduct fg.2) :=
  (continuous_source_tensorProduct n m).comp
    (((continuous_source_osConj n).comp continuous_fst).prodMk continuous_snd)

theorem tendsto_source_osConjTensorProduct_zeroDiagonal {n m : ℕ}
    {f : ℕ → SchwartzNPoint 3 n} {g : ℕ → SchwartzNPoint 3 m}
    {f₀ : SchwartzNPoint 3 n} {g₀ : SchwartzNPoint 3 m}
    (hf : ∀ j, tsupport (f j) ⊆ OrderedPositiveTimeRegion 3 n)
    (hg : ∀ j, tsupport (g j) ⊆ OrderedPositiveTimeRegion 3 m)
    (hf₀ : tsupport f₀ ⊆ OrderedPositiveTimeRegion 3 n)
    (hg₀ : tsupport g₀ ⊆ OrderedPositiveTimeRegion 3 m)
    (hflim : Tendsto f atTop (𝓝 f₀)) (hglim : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun j => ZeroDiagonalSchwartz.ofClassical ((f j).osConjTensorProduct (g j)))
      atTop (𝓝 (ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct g₀))) := by
  have hlim : Tendsto (fun j => (f j).osConjTensorProduct (g j))
      atTop (𝓝 (f₀.osConjTensorProduct g₀)) := by
    exact ((continuous_source_osConjTensorProduct n m).continuousAt
      (x := (f₀, g₀))).tendsto.comp (f := fun j => (f j, g j))
        (hflim.prodMk_nhds hglim)
  have hval (j : ℕ) :
      (ZeroDiagonalSchwartz.ofClassical ((f j).osConjTensorProduct (g j))).1 =
        (f j).osConjTensorProduct (g j) :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        _ _ (hf j) (hg j))
  have hval₀ : (ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct g₀)).1 =
      f₀.osConjTensorProduct g₀ :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        _ _ hf₀ hg₀)
  apply (@tendsto_subtype_rng (SchwartzNPoint 3 (n + m)) _ ℕ
    (fun h => VanishesToInfiniteOrderOnCoincidence h) atTop
    (fun j => ZeroDiagonalSchwartz.ofClassical ((f j).osConjTensorProduct (g j)))
    (ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct g₀))).mpr
  simp only [hval, hval₀]
  exact hlim

end YangMills.OSRecon



noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace YangMills.OSRecon

/-- Positivity on compact ordered-support tests extends to the complete source
Schwartz support sector by continuity on the zero-diagonal test spaces. -/
theorem source_reflection_positive_of_compact
    (S : (n : ℕ) → ZeroDiagonalSchwartz 3 n →L[ℂ] ℂ)
    (hcompact : ∀ (N : ℕ) (degree : Fin N → ℕ)
      (h : ∀ i, SchwartzNPoint 3 (degree i)),
      (∀ i, HasCompactSupport (h i)) →
      (∀ i, tsupport (h i) ⊆ OrderedPositiveTimeRegion 3 (degree i)) →
      ∀ c : Fin N → ℂ,
        0 ≤ (∑ i, ∑ j, star (c i) * c j * S (degree i + degree j)
          (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j)))).re)
    {N : ℕ} (degree : Fin N → ℕ) (h : ∀ i, SchwartzNPoint 3 (degree i))
    (hh : ∀ i, tsupport (h i) ⊆ OrderedPositiveTimeRegion 3 (degree i))
    (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, star (c i) * c j * S (degree i + degree j)
      (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j)))).re := by
  choose g hg hlim using fun i => exists_compact_ordered_sequence (h i) (hh i)
  have hterm (i j : Fin N) :
      Tendsto (fun k => star (c i) * c j * S (degree i + degree j)
        (ZeroDiagonalSchwartz.ofClassical ((g i k).osConjTensorProduct (g j k))))
      atTop (𝓝 (star (c i) * c j * S (degree i + degree j)
        (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j))))) := by
    have ht := tendsto_source_osConjTensorProduct_zeroDiagonal
      (fun k => (hg i k).2.1) (fun k => (hg j k).2.1) (hh i) (hh j) (hlim i) (hlim j)
    exact (((S (degree i + degree j)).continuous.tendsto _).comp
      (f := fun k => ZeroDiagonalSchwartz.ofClassical
        ((g i k).osConjTensorProduct (g j k))) ht).const_mul _
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun j _ => hterm i j
  have hreal := (Complex.continuous_re.tendsto _).comp hsum
  apply ge_of_tendsto hreal
  exact Eventually.of_forall fun k =>
    hcompact N degree (fun i => g i k) (fun i => (hg i k).1)
      (fun i => (hg i k).2.1) c

/-- The finite-family positivity statement implies the literal source `E2`
inner product for every Borchers sequence with ordered positive-time support. -/
theorem source_OSInnerProduct_nonneg_of_family
    (S : (n : ℕ) → ZeroDiagonalSchwartz 3 n →L[ℂ] ℂ)
    (hfamily : ∀ (N : ℕ) (degree : Fin N → ℕ)
      (h : ∀ i, SchwartzNPoint 3 (degree i)),
      (∀ i, tsupport (h i) ⊆ OrderedPositiveTimeRegion 3 (degree i)) →
      ∀ c : Fin N → ℂ,
        0 ≤ (∑ i, ∑ j, star (c i) * c j * S (degree i + degree j)
          (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j)))).re)
    (F : BorchersSequence 3)
    (hF : ∀ n, tsupport (F.funcs n) ⊆ OrderedPositiveTimeRegion 3 n) :
    0 ≤ (OSInnerProduct 3 (fun n h => S n h) F F).re := by
  have h := hfamily (F.bound + 1) (fun i => i.val) (fun i => F.funcs i.val)
    (fun i => hF i.val) (fun _ => 1)
  simpa only [star_one, one_mul, OSInnerProduct, ← Fin.sum_univ_eq_sum_range] using h

end YangMills.OSRecon
