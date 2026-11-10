import YM.Spec.Closed
import ImportedAFGauge

/-! Exact selected declarations from the group specification. SpaceTime is
the same Euclidean four-space; the OSforGFF measure layer is not imported. -/
open Filter Topology
noncomputable section
abbrev SpaceTime := EuclideanSpace ℝ (Fin 4)

def uvLog (Λ : ℝ) (x : SpaceTime) : ℝ :=
  Real.log (1 / (Λ * ‖x‖))

def freeTraceTwoPoint : ℝ := 3 / Real.pi ^ 4

theorem freeTraceTwoPoint_pos : 0 < freeTraceTwoPoint := by
  have := Real.pi_pos
  unfold freeTraceTwoPoint
  positivity

def KernelUVPowerLaw (K : SpaceTime → ℝ) : Prop :=
  ∃ A Λ : ℝ, 0 < A ∧ 0 < Λ ∧
    Tendsto
      (fun x : SpaceTime =>
        K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ))
      (𝓝[≠] (0 : SpaceTime)) (𝓝 A)

def KernelUVAsymptoticallyFree (K : SpaceTime → ℝ)
    (G : GaugeGroupData) : Prop :=
  ∃ A Λ : ℝ, 0 < A ∧ 0 < Λ ∧
    Tendsto
      (fun x : SpaceTime =>
        K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ))
      (𝓝[≠] (0 : SpaceTime)) (𝓝 A) ∧
    Tendsto
      (fun x : SpaceTime =>
        (K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ) - A) *
          uvLog Λ x / Real.log (uvLog Λ x))
      (𝓝[≠] (0 : SpaceTime)) (𝓝 (-(G.betaOne / G.betaZero ^ 2) * A))

lemma norm_tendsto_punctured :
    Filter.Tendsto (fun x : SpaceTime => ‖x‖)
      (nhdsWithin (0 : SpaceTime) {0}ᶜ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Filter.Tendsto (fun x : SpaceTime => ‖x‖) (nhds 0) (nhds ‖(0 : SpaceTime)‖) :=
      continuous_norm.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · exact eventually_mem_nhdsWithin.mono fun x hx => norm_pos_iff.mpr hx

/-- The asymptotic-freedom logarithm diverges at short distance:
`uvLog Λ x → ∞` as `x → 0` through nonzero points. -/
lemma uvLog_tendsto_atTop {Λ : ℝ} (hΛ : 0 < Λ) :
    Filter.Tendsto (fun x : SpaceTime => uvLog Λ x)
      (nhdsWithin (0 : SpaceTime) {0}ᶜ) Filter.atTop := by
  have hmul : Filter.Tendsto (fun t : ℝ => Λ * t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Filter.Tendsto (fun t : ℝ => Λ * t) (nhds 0) (nhds (Λ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · exact eventually_mem_nhdsWithin.mono fun t ht => mul_pos hΛ ht
  have hinv : Filter.Tendsto (fun t : ℝ => (Λ * t)⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp hmul
  have hlog : Filter.Tendsto (fun t : ℝ => Real.log (Λ * t)⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    Real.tendsto_log_atTop.comp hinv
  have := hlog.comp norm_tendsto_punctured
  refine this.congr fun x => ?_
  simp [uvLog, Function.comp, one_div]
