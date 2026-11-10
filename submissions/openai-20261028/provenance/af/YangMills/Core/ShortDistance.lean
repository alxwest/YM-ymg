/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import OSforGFF.Schwinger.TwoPoint
import YangMills.Core.GaugeGroup

/-!
# Short-distance identification: asymptotic freedom for `Θ = T^μ_μ`

A theory satisfying the OS axioms with a mass gap could a priori be anything
(e.g. a massive free field, or a `P(φ)₂`-style model placed in disguise).
What identifies it as *Yang-Mills* is that the short-distance behavior of its
correlation functions is asymptotically approximated by renormalized
perturbation theory — the theory is asymptotically free, with the specific
perturbative data of gauge theory.

This file states that criterion for the two-point function of the trace of
the stress tensor, `Θ = T^μ_μ`.  The distinction from bare `tr F²` is not
cosmetic and the two are *not* interchangeable normalizations: `Θ` is the
RG-invariant combination `(β(g)/2g)·tr F²`, which is what gives it a
protected dimension and the clean `ℓ⁻²` law derived below.  Bare `tr F²`
carries an anomalous dimension and has no scale-free short-distance law of
this shape.

## The prediction

`tr F²` has canonical dimension 4 and its renormalization is tied to the beta
function (`(β(g)/g)·tr F²` is RG-invariant).  Renormalization-group-improved
perturbation theory therefore predicts, for `x → 0` and any fixed
normalization of the field,

  `S₂(x) = A · ‖x‖⁻⁸ · ℓ(x)⁻² · (1 − (b₁/b₀²)·(log ℓ(x))/ℓ(x) + O(1/ℓ(x)))`

where `ℓ(x) = log(1/(Λ‖x‖))` for a dynamically generated scale `Λ > 0`
(the running coupling at separation `x` is `ḡ²(x) ≈ 16π²/(2 b₀ ℓ(x))`, and
the correlator carries a factor `ḡ⁴`).  We encode:

1. `UVPowerLaw` — `S₂(x)·‖x‖⁸·ℓ(x)² → A > 0`: the canonical power `‖x‖⁻⁸`
   with *exactly two* powers of the asymptotic-freedom logarithm.  A free
   massive scalar (`S₂ ~ ‖x‖⁻²`), a generalized free field, or a nontrivial
   UV fixed point (anomalous power of `‖x‖`, no pure logs) all fail this.
2. `UVAsymptoticallyFree` — additionally, the second-order coefficient: the
   relative correction `−(b₁/b₀²)·(log ℓ)/ℓ`.

## Caveats (statement version 0)

* By `GaugeGroupData.betaOne_div_betaZero_sq`, `b₁/b₀² = 102/121` for every
  compact simple `G` — pure Yang-Mills has *universal* two-point UV shape in
  the `tr F²` channel through second order.  So this criterion pins down
  "asymptotically free gauge theory", not which group; the `G`-dependence of
  the statement currently enters only through the intended constructive
  route.  Sharpening the identification (multi-operator correlators, Wilson
  loops, order-by-order matching to a formalized perturbative expansion) is
  milestone M4 in `docs/roadmap.md`.
* The choice of `Λ` is a convention; a change `Λ → Λ'` shifts `ℓ` by a
  constant, which is absorbed by the stated error orders.
-/

open MeasureTheory Topology Filter

noncomputable section

/-- The asymptotic-freedom logarithm `ℓ(x) = log(1/(Λ‖x‖))`, positive for
`‖x‖ < 1/Λ` and `→ ∞` as `x → 0`.  `1/ℓ(x)` is (up to the constant
`16π²/(2b₀)`) the running coupling `ḡ²` at separation `x`. -/
def uvLog (Λ : ℝ) (x : SpaceTime) : ℝ :=
  Real.log (1 / (Λ * ‖x‖))

/-- Leading amplitude of the trace-channel two-point function per gluon:
`⟨Θ(x)Θ(0)⟩ ~ dimG · freeTraceTwoPoint · ‖x‖⁻⁸ ℓ⁻²`, where `Θ = T^μ_μ`.

Derivation: the trace anomaly gives `Θ = (β(g)/2g) F²` and with
`ḡ²(x) = 8π²/(b₀ ℓ)` the `b₀` cancels: `Θ ≈ −F²/(4ℓ)` asymptotically.  The
free-gluon Wick contraction from `⟨F_{μν}(x)F_{σρ}(0)⟩ =
(2/S₄‖x‖⁴)(I_{μσ}I_{νρ} − I_{μρ}I_{νσ})` [OP eq. (5.15)] gives
`⟨F²(x)F²(0)⟩ = 2·(2/S₄)²·24·dimG·‖x‖⁻⁸ = (48/π⁴)·dimG·‖x‖⁻⁸`
(tensor contraction `(I I − I I)² = 16 − 2·4 + 16 = 24`), hence the
amplitude `48/(16π⁴) = 3/π⁴` per gluon. -/
def freeTraceTwoPoint : ℝ := 3 / Real.pi ^ 4

theorem freeTraceTwoPoint_pos : 0 < freeTraceTwoPoint := by
  have := Real.pi_pos
  unfold freeTraceTwoPoint
  positivity

/-- Kernel-parametric leading short-distance criterion:
`K(x) · ‖x‖⁸ · ℓ(x)² → A` for some `A > 0`, `Λ > 0`.  The v4 primary
form — the argument is any two-point kernel (a Schwinger system's
`K₂`, or a measure's `SchwingerTwoPointFunction`). -/
def KernelUVPowerLaw (K : SpaceTime → ℝ) : Prop :=
  ∃ A Λ : ℝ, 0 < A ∧ 0 < Λ ∧
    Tendsto
      (fun x : SpaceTime =>
        K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ))
      (𝓝[≠] (0 : SpaceTime)) (𝓝 A)

/-- Leading short-distance behavior of an asymptotically free `tr F²`
channel, measure form (delegates to the kernel-parametric
criterion). -/
def UVPowerLaw (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  KernelUVPowerLaw (SchwingerTwoPointFunction dμ_config)

/-- Short-distance behavior asymptotically approximated by renormalized
perturbation theory, through second order in RG-improved perturbation
theory: the leading power law of `UVPowerLaw`, together with the two-loop
`(log ℓ)/ℓ` correction with coefficient `−b₁/b₀²`.

This is the (version 0) formalization of the Jaffe-Witten requirement that
the constructed theory's short-distance correlations match perturbative
Yang-Mills.  Kernel-parametric (v4 primary form). -/
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

/-- **The leading-log tower, order two.**  `KernelUVAsymptoticallyFree`
pins the amplitude and the `(log ℓ)/ℓ` coefficient; this adds the next
universal structure.

**Which structures are universal.**  Writing `ℓ = uvLog Λ x` and
`R = K·‖x‖⁸·ℓ²`, the renormalization-group improved expansion of `R/A` in
powers of `1/ℓ` has, at order `1/ℓ^k`, exactly `k+1` structures
`(log ℓ)^m/ℓ^k` for `m ≤ k` — and exactly one of them, the leading log
`m = k`, is fixed by `b₀` and `b₁` alone.  The rest are absorbed by the
`Λ` convention and by the scheme-dependent higher coefficients.  At order
`1/ℓ` this recovers the existing condition: the `(log ℓ)/ℓ` coefficient is
`−b₁/b₀²`, while the `1/ℓ` coefficient is `(−C + r₁/2)/b₀`, pure
convention, which is exactly what the existential over `Λ` absorbs.

At order `1/ℓ²` the universal coefficient is `3b₁²/(4b₀⁴)`.  The
three-loop coefficient `b₂` and the perturbative correlator coefficients
enter only the lower structures `(log ℓ)/ℓ²` and `1/ℓ²`, so they cannot
move it.

**The third clause also fixes `Λ`, and this is deliberate.**  Subtracting
the first two terms leaves `A(c₁₀/ℓ + c₂₂(log ℓ)²/ℓ² + ⋯)`, and multiplying
by `ℓ²/(log ℓ)²` sends the `c₁₀` term to `c₁₀·ℓ/(log ℓ)²`, which diverges
unless `c₁₀ = 0`.  So the limit exists only for the `Λ` that kills the
`1/ℓ` constant — the condition is satisfiable (`c₁₀(Λe^δ) = c₁₀(Λ) − 2δ`, so exactly
one `Λ` works) and the existential picks that
one.  This is the `c₁₀ = 0` convention already used for the deep expansion
in `Statement/GroupIdentification.lean`, where `UniversalUVCoeffs.model`
carries no `1/ℓ` constant term, so the two layers agree.  The value
`3b₁²/(4b₀⁴)` is unaffected: it does not depend on the `Λ` convention.  Derived and checked in `scripts/check_uv_tower_orders.py`; the
inverse coupling has no `(log ℓ)²/ℓ` term (`α = 0`), which is why the
value is what it is.

**Why this is a separate predicate.**  Exactly as with
`HasCanonicalUVAmplitudes`, an exact equality is unsatisfiable if the
constant is wrong, and each further order is another convention that can
be got wrong with no witness to catch it.  The master statement therefore
requires only `KernelUVAsymptoticallyFree`; this is a named strengthening,
available to a construction that can supply it. -/
def KernelUVLeadingLogTwo (K : SpaceTime → ℝ) (G : GaugeGroupData) : Prop :=
  ∃ A Λ : ℝ, 0 < A ∧ 0 < Λ ∧
    Tendsto
      (fun x : SpaceTime => K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ))
      (𝓝[≠] (0 : SpaceTime)) (𝓝 A) ∧
    Tendsto
      (fun x : SpaceTime =>
        (K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ) - A) *
          uvLog Λ x / Real.log (uvLog Λ x))
      (𝓝[≠] (0 : SpaceTime)) (𝓝 (-(G.betaOne / G.betaZero ^ 2) * A)) ∧
    Tendsto
      (fun x : SpaceTime =>
        (K x * ‖x‖ ^ (8 : ℕ) * uvLog Λ x ^ (2 : ℕ) - A
          + (G.betaOne / G.betaZero ^ 2) * A
              * Real.log (uvLog Λ x) / uvLog Λ x) *
          uvLog Λ x ^ (2 : ℕ) / Real.log (uvLog Λ x) ^ (2 : ℕ))
      (𝓝[≠] (0 : SpaceTime))
      (𝓝 (3 * G.betaOne ^ (2 : ℕ) / (4 * G.betaZero ^ (4 : ℕ)) * A))

/-! ### The law for a general operator

`KernelUVAsymptoticallyFree` is the case of an operator of dimension `4`
whose two-point function carries two powers of the running coupling.  Both
numbers are properties of the operator, and the law generalizes with them. -/

/-- **The short-distance law at a general pair of exponents.**

"General" is bounded: `p q : ℕ` covers integer power laws and integer powers
of the coupling, which is the family the trace anomaly sits in.  Genuinely
anomalous (non-integer) exponents are outside it.

`K(x)·‖x‖^p·ℓ(x)^q → A > 0`, with relative two-loop correction
`−q·b₁/(2b₀²)·(log ℓ)/ℓ`, where

* `p = 2Δ` with `Δ` the operator's dimension;
* `q` is the power of the running coupling `ḡ²` its two-point function
  carries.

The `2` in the two-loop coefficient is not a typo and is worth seeing once.
The standard two-loop running is written in `L = log(μ²/Λ²)`, and
`(ḡ²)^q ∝ L^{-q}[1 − q(b₁/b₀²)(log L)/L]`.  Here `ℓ = log(1/(Λ‖x‖)) = L/2`,
so `1/L = 1/(2ℓ)` and the factor of `q` is halved on the way in.  At `q = 2`
the halving cancels the squaring and the coefficient is `−b₁/b₀²`, which is
why `KernelUVAsymptoticallyFree` looks like it is missing a factor and is
not.  Checked in `scripts/check_uv_tower_orders.py`. -/
def KernelUVLawAt (K : SpaceTime → ℝ) (G : GaugeGroupData) (p q : ℕ) : Prop :=
  ∃ A Λ : ℝ, 0 < A ∧ 0 < Λ ∧
    Tendsto
      (fun x : SpaceTime => K x * ‖x‖ ^ p * uvLog Λ x ^ q)
      (𝓝[≠] (0 : SpaceTime)) (𝓝 A) ∧
    Tendsto
      (fun x : SpaceTime =>
        (K x * ‖x‖ ^ p * uvLog Λ x ^ q - A) *
          uvLog Λ x / Real.log (uvLog Λ x))
      (𝓝[≠] (0 : SpaceTime))
      (𝓝 (-((q : ℝ) * G.betaOne / (2 * G.betaZero ^ 2)) * A))

/-- **The trace-anomaly case is `(p, q) = (8, 2)`.**  Dimension four gives
`p = 8`; the two anomaly factors, one per insertion, give `q = 2`.

Proving this rather than asserting it is the point of having the general
form: it exercises the `−q·b₁/(2b₀²)` rule at the one instance the
statement uses. -/
theorem kernelUVLawAt_eight_two (K : SpaceTime → ℝ) (G : GaugeGroupData) :
    KernelUVLawAt K G 8 2 ↔ KernelUVAsymptoticallyFree K G := by
  have hb : G.betaZero ≠ 0 := ne_of_gt G.betaZero_pos
  have hcoef : ∀ A : ℝ,
      -(((2 : ℕ) : ℝ) * G.betaOne / (2 * G.betaZero ^ 2)) * A
        = -(G.betaOne / G.betaZero ^ 2) * A := by
    intro A
    push_cast
    field_simp
  unfold KernelUVLawAt KernelUVAsymptoticallyFree
  constructor
  · rintro ⟨A, Λ, hA, hΛ, h0, h1⟩
    exact ⟨A, Λ, hA, hΛ, h0, (hcoef A) ▸ h1⟩
  · rintro ⟨A, Λ, hA, hΛ, h0, h1⟩
    exact ⟨A, Λ, hA, hΛ, h0, (hcoef A).symm ▸ h1⟩

/-- Order two is at least as strong as order one: it repeats the first two
clauses verbatim. -/
theorem KernelUVAsymptoticallyFree.of_leadingLogTwo {K : SpaceTime → ℝ}
    {G : GaugeGroupData} (h : KernelUVLeadingLogTwo K G) :
    KernelUVAsymptoticallyFree K G := by
  obtain ⟨A, Λ, hA, hΛ, h0, h1, -⟩ := h
  exact ⟨A, Λ, hA, hΛ, h0, h1⟩

/-- Measure form (delegates to the kernel-parametric criterion). -/
def UVAsymptoticallyFree (dμ_config : ProbabilityMeasure FieldConfiguration)
    (G : GaugeGroupData) : Prop :=
  KernelUVAsymptoticallyFree (SchwingerTwoPointFunction dμ_config) G

/-- The full kernel criterion implies the leading power law. -/
theorem KernelUVAsymptoticallyFree.kernelUVPowerLaw
    {K : SpaceTime → ℝ} {G : GaugeGroupData}
    (h : KernelUVAsymptoticallyFree K G) : KernelUVPowerLaw K := by
  obtain ⟨A, Λ, hA, hΛ, hlim, -⟩ := h
  exact ⟨A, Λ, hA, hΛ, hlim⟩

/-- The full criterion implies the leading power law (measure form). -/
theorem UVAsymptoticallyFree.uvPowerLaw
    {dμ_config : ProbabilityMeasure FieldConfiguration} {G : GaugeGroupData}
    (h : UVAsymptoticallyFree dμ_config G) : UVPowerLaw dμ_config :=
  h.kernelUVPowerLaw

/-- The norm map sends the punctured neighborhood of `0` in spacetime to
the right-neighborhood of `0` in `ℝ`. -/
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

end
