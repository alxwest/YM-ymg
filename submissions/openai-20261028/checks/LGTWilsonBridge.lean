import ImportedLGTData
import WilsonBridge

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace YMLGTBridge
variable (g : YangMills.GaugeGroup) (l : ℕ+)

def linkEquiv : LatticeLink 4 l.val ≃ (YangMills.Site l × YangMills.Axis) where
  toFun e := (e.site, e.dir)
  invFun e := ⟨e.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (LatticeLink 4 l.val) := Fintype.ofEquiv _ (linkEquiv l).symm

def faceEquiv : LatticePlaquette 4 l.val ≃ (YangMills.Site l × YangMills.Directions) where
  toFun p := (p.site, ⟨(p.dir1, p.dir2), p.h_lt⟩)
  invFun p := ⟨p.1, p.2.val.1, p.2.val.2, p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (LatticePlaquette 4 l.val) := Fintype.ofEquiv _ (faceEquiv l).symm

instance : HasGaugeTrace g.image (g.n + 1) where
  rep := { toFun := fun u => u.val.val, map_one' := rfl, map_mul' := fun _ _ => rfl }

instance : HasHaarProbability g.image where
  haar := g.core.probHaar
  isProb := inferInstanceAs (IsProbabilityMeasure g.core.probHaar)

/-- Reindexing of the identical link variables; no gauge fixing or averaging. -/
def configEquiv : GaugeConnection g.image 4 l.val ≃ᵐ YangMills.Configuration g l :=
  MeasurableEquiv.piCongrLeft (fun _ => g.image) (linkEquiv l)

theorem shift_eq (x : YangMills.Site l) (i : YangMills.Axis) :
    siteShift 4 l.val x i = x + Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst j; simp [siteShift]
  · simp [siteShift, Function.update_of_ne h, Pi.single_eq_of_ne h]

theorem plaquette_eq (U : GaugeConnection g.image 4 l.val)
    (p : LatticePlaquette 4 l.val) :
    plaquetteHolonomy U p = YangMills.plaquette (configEquiv g l U) p.site p.dir1 p.dir2 := by
  change U ⟨p.site,p.dir1⟩ * U ⟨siteShift 4 l.val p.site p.dir1,p.dir2⟩ *
    (U ⟨siteShift 4 l.val p.site p.dir2,p.dir1⟩)⁻¹ * (U ⟨p.site,p.dir2⟩)⁻¹ =
    U ⟨p.site,p.dir1⟩ * (U ⟨p.site + Pi.single p.dir1 1,p.dir2⟩ *
      ((U ⟨p.site + Pi.single p.dir2 1,p.dir1⟩)⁻¹ * (U ⟨p.site,p.dir2⟩)⁻¹))
  rw [← shift_eq, ← shift_eq]
  simp only [mul_assoc]

theorem gauge_eq (t : GaugeTransform g.image 4 l.val)
    (U : GaugeConnection g.image 4 l.val) :
    configEquiv g l (gaugeTransformConnection t U) =
      YM.Lattice.gauge t (configEquiv g l U) := by
  funext e
  rcases e with ⟨x, i⟩
  change t x * U ⟨x,i⟩ * (t (siteShift 4 l.val x i))⁻¹ =
    t x * U ⟨x,i⟩ * (t (x + Pi.single i 1))⁻¹
  rw [shift_eq]

/-- The lgt coefficient multiplies an unnormalized trace cost. -/
theorem action_eq (β : ℝ) (U : GaugeConnection g.image 4 l.val) :
    wilsonAction g.image (g.n+1) 4 l.val β U Finset.univ =
      (β * (g.n+1 : ℕ)) * YangMills.wilsonEnergy (configEquiv g l U) := by
  classical
  unfold wilsonAction YangMills.wilsonEnergy
  rw [Finset.mul_sum, ← Equiv.sum_comp (faceEquiv l)]
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquette_eq]
  let t := (YangMills.plaquette (configEquiv g l U) p.site p.dir1 p.dir2).val.val.trace.re
  change β * ((g.n+1 : ℕ) - t) = (β * (g.n+1 : ℕ)) * (1 - t / (g.n+1 : ℕ))
  have hn : ((g.n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem weight_eq (β : ℝ) (U : GaugeConnection g.image 4 l.val) :
    boltzmannWeight g.image (g.n+1) 4 l.val β U Finset.univ =
      YM.Wilson.bare (G := g.core) (β * (g.n+1 : ℕ)) (configEquiv g l U) := by
  unfold boltzmannWeight
  rw [action_eq, YangMills.energy_eq]
  simp [YM.Wilson.bare, neg_mul]

theorem prior_preserving :
    MeasurePreserving (configEquiv g l) (productHaar g.image 4 l.val)
      (YM.Wilson.prior g.core l) :=
  measurePreserving_piCongrLeft (fun _ => g.core.probHaar) (linkEquiv l)

theorem partition_eq (β : ℝ) :
    partitionFn g.image (g.n+1) 4 l.val β Finset.univ =
      YM.Wilson.partition g.core l (β * (g.n+1 : ℕ)) := by
  unfold partitionFn YM.Wilson.partition
  simp_rw [weight_eq]
  exact (prior_preserving g l).integral_comp (configEquiv g l).measurableEmbedding _

theorem density_eq (β : ℝ) (U : GaugeConnection g.image 4 l.val) :
    ENNReal.ofReal (ymDensity g.image (g.n+1) 4 l.val β Finset.univ U) =
      YM.Wilson.weight (G := g.core) (β * (g.n+1 : ℕ)) (configEquiv g l U) := by
  unfold ymDensity YM.Wilson.weight
  rw [weight_eq, partition_eq]

/-- Exact equality of probability laws under the link reindexing and beta conversion. -/
theorem law_preserving (β : ℝ) :
    MeasurePreserving (configEquiv g l)
      (ymMeasure g.image (g.n+1) 4 l.val β Finset.univ)
      (YangMills.wilsonLaw g l (β * (g.n+1 : ℕ)) g.core.probHaar) := by
  refine ⟨(configEquiv g l).measurable, ?_⟩
  rw [YangMills.law_eq]
  ext s hs
  rw [Measure.map_apply (configEquiv g l).measurable hs, ymMeasure,
    withDensity_apply _ ((configEquiv g l).measurable hs), YM.Wilson.law]
  erw [withDensity_apply _ hs]
  simp_rw [density_eq]
  exact ((prior_preserving g l).restrict_preimage_emb
    (configEquiv g l).measurableEmbedding s).lintegral_comp_emb
      (configEquiv g l).measurableEmbedding _

/-- Integrability is transported too, so equality need not be read as an equality
of totalized integrals of nonintegrable functions. -/
theorem integrable_iff (β : ℝ) (f : YangMills.Configuration g l → ℂ) :
    Integrable (fun U => f (configEquiv g l U))
      (ymMeasure g.image (g.n+1) 4 l.val β Finset.univ) ↔
    Integrable f (YangMills.wilsonLaw g l (β * (g.n+1 : ℕ)) g.core.probHaar) :=
  (law_preserving g l β).integrable_comp_emb (configEquiv g l).measurableEmbedding

theorem expectation_eq (β : ℝ) (f : YangMills.Configuration g l → ℂ) :
    (∫ U, f (configEquiv g l U) ∂ymMeasure g.image (g.n+1) 4 l.val β Finset.univ) =
      ∫ U, f U ∂YangMills.wilsonLaw g l (β * (g.n+1 : ℕ)) g.core.probHaar :=
  (law_preserving g l β).integral_comp (configEquiv g l).measurableEmbedding f

end YMLGTBridge
