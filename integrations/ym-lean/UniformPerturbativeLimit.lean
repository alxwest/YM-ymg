import YangMills.ExistenceOnly

set_option autoImplicit false
set_option warningAsError true

/-!
# A uniform finite-regulator estimate survives the continuum limit

This module proves a genuine limit-passage step toward the UNCHANGED
ym-lean existence-only target. It does not assert the missing estimates.
The coefficient limits must be the prescribed target coefficients;
one cannot substitute a freely chosen perturbative series.

Crucial quantifier order: the small-scale radius is chosen before the
regulator tends to its limit. The regulator threshold may depend on the
fixed scale and test. The regulator filter is explicitly nontrivial.

The original source has formal all-order diagrams at a finite regulator
and leading continuum results. Neither fact supplies the uniform
remainder estimates below; those are a remaining analytic obligation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace YMYMG.Existence

variable {I : Type*} {L : Filter I} [L.NeBot]

/-- A finite-order remainder bound transfers to the same limit of the
observations and coefficient functions. The conclusion uses the *fixed*
coefficient limits, not coefficients selected after seeing the observation. -/
theorem remainder_bound_of_limits
    (observation : I → ℂ) (limitObservation : ℂ)
    (coefficient : I → ℕ → ℂ) (limitCoefficient : ℕ → ℂ)
    (coupling : ℝ) (order : ℕ) (bound : ℝ)
    (hObservation : Tendsto observation L (𝓝 limitObservation))
    (hCoefficient : ∀ k ∈ Finset.range (order + 1),
      Tendsto (fun i => coefficient i k) L (𝓝 (limitCoefficient k)))
    (hBound : ∀ᶠ i in L,
      ‖observation i - ∑ k ∈ Finset.range (order + 1),
        (coupling : ℂ) ^ k * coefficient i k‖ ≤ bound) :
    ‖limitObservation - ∑ k ∈ Finset.range (order + 1),
      (coupling : ℂ) ^ k * limitCoefficient k‖ ≤ bound := by
  have hSum := tendsto_finsetSum (Finset.range (order + 1))
    (fun k hk => (hCoefficient k hk).const_mul ((coupling : ℂ) ^ k))
  exact le_of_tendsto (hObservation.sub hSum).norm hBound

/-- The uniform radius in the finite-regulator hypothesis yields the
all-real-scale, every-finite-order remainder relation. This is stronger
than convergence along a selected sequence of scales. -/
theorem all_orders_of_uniform_regulated_estimates
    (observation : I → ℝ → ℂ) (limitObservation : ℝ → ℂ)
    (coefficient : I → ℕ → ℂ) (limitCoefficient : ℕ → ℂ)
    (coupling : ℝ → ℝ)
    (hObservation : ∀ scale : ℝ, 0 < scale → scale < 1 →
      Tendsto (fun i => observation i scale) L (𝓝 (limitObservation scale)))
    (hCoefficient : ∀ k, Tendsto (fun i => coefficient i k) L
      (𝓝 (limitCoefficient k)))
    (hUniform : ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ scale : ℝ, 0 < scale → scale < delta →
      ∀ᶠ i in L,
        ‖observation i scale - ∑ k ∈ Finset.range (order + 1),
          (coupling scale : ℂ) ^ k * coefficient i k‖ ≤
            epsilon * coupling scale ^ order) :
    ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ scale : ℝ, 0 < scale → scale < delta →
        ‖limitObservation scale - ∑ k ∈ Finset.range (order + 1),
          (coupling scale : ℂ) ^ k * limitCoefficient k‖ ≤
            epsilon * coupling scale ^ order := by
  intro order epsilon hEpsilon
  obtain ⟨delta, hDelta, hDeltaOne, hBound⟩ := hUniform order epsilon hEpsilon
  refine ⟨delta, hDelta, hDeltaOne, ?_⟩
  intro scale hScale hScaleDelta
  exact remainder_bound_of_limits (fun i => observation i scale)
    (limitObservation scale) coefficient limitCoefficient (coupling scale)
    order (epsilon * coupling scale ^ order)
    (hObservation scale hScale (lt_of_lt_of_le hScaleDelta hDeltaOne))
    (fun k _ => hCoefficient k) (hBound scale hScale hScaleDelta)


/-- Regulator data for one fixed physical test and its fixed prescribed
coefficient sequence. The eventual regulator threshold may depend on
scale, but delta must not depend on the regulator. -/
structure RegulatedExpansion (L : Filter I) (coupling : ℝ → ℝ)
    (limitObservation : ℝ → ℂ) (limitCoefficient : ℕ → ℂ) where
  observation : I → ℝ → ℂ
  coefficient : I → ℕ → ℂ
  observation_limit : ∀ scale : ℝ, 0 < scale → scale < 1 →
    Tendsto (fun i => observation i scale) L (𝓝 (limitObservation scale))
  coefficient_limit : ∀ k,
    Tendsto (fun i => coefficient i k) L (𝓝 (limitCoefficient k))
  uniform_remainder : ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
    ∀ scale : ℝ, 0 < scale → scale < delta →
    ∀ᶠ i in L,
      ‖observation i scale - ∑ k ∈ Finset.range (order + 1),
        (coupling scale : ℂ) ^ k * coefficient i k‖ ≤
          epsilon * coupling scale ^ order

/-- This proof uses the exact continuum coefficient and vacuum-observation
slots already present in ym-lean. It never changes the acceptance target. -/
theorem RegulatedExpansion.continuum
    {coupling : ℝ → ℝ} {observation : ℝ → ℂ} {coefficient : ℕ → ℂ}
    (D : RegulatedExpansion L coupling observation coefficient) :
    ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ scale : ℝ, 0 < scale → scale < delta →
        ‖observation scale - ∑ k ∈ Finset.range (order + 1),
          (coupling scale : ℂ) ^ k * coefficient k‖ ≤
            epsilon * coupling scale ^ order :=
  all_orders_of_uniform_regulated_estimates D.observation observation
    D.coefficient coefficient coupling D.observation_limit
    D.coefficient_limit D.uniform_remainder

open YangMills YangMills.PerturbativeFlow

/-- Exact OPE-matching predicate required by GeneratedMatching.
This closes the LIMIT PASSAGE only, conditional on regulator-uniform
bounds with the prescribed coefficient limits, for every physical test. -/
theorem allOrderMultiMatch_of_regulated
    {G : CompactSimpleGaugeGroup} {m : ℕ}
    {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    (F : FilteredRG.Frame labels reference betaSeries gammaSeries)
    (coeff : (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (physical : ℕ → (n : ℕ) → (Fin n → Fin m) → Fin m → Fin m → OPE.MultiDistribution n)
    (hLocal : ∀ n inputs last output, OPE.IsLocalMultiDistribution (coeff n inputs last output))
    (hPhysical : ∀ order n inputs last output,
      OPE.IsLocalMultiDistribution (physical order n inputs last output))
    (hRegulated : ∀ n, 0 < n → ∀ inputs last output (test : OPE.RelativeTest n),
      OPE.MultiOffDiagonal test → Nonempty (RegulatedExpansion L
        (fun scale => F.running.coupling (RG.time scale))
        (fun scale => FilteredRG.strippedMultiPairing F coeff scale n inputs last output test)
        (fun k => physical k n inputs last output test))) :
    FilteredRG.AllOrderMultiMatch F coeff physical := by
  refine ⟨hLocal, hPhysical, ?_⟩
  intro n hn inputs last output test hTest
  obtain ⟨D⟩ := hRegulated n hn inputs last output test hTest
  exact D.continuum

/-- Exact actual-vacuum-word matching predicate, NOT merely an OPE
coefficient identity. The hypotheses must hold for the SAME physical
continuation V, running frame F, and fixed generated series. -/
theorem allOrderVacuumWordMatch_of_regulated
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Q : WightmanData H} {G : CompactSimpleGaugeGroup}
    {C : RenormalizedCompositeMap Q G} {m : ℕ}
    {labels : Fin m → InvariantInsertionLabel G}
    {reference : RenormalizationScale} {betaSeries : ℕ → ℝ}
    {gammaSeries : RenormalizationScale → ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} (V : PhysicalWords.VacuumWordContinuation K)
    (F : FilteredRG.Frame labels reference betaSeries gammaSeries)
    (rotation : Wick.LabelRotation labels)
    (series : ℕ → (n : ℕ) → (Fin (n+1) → Fin m) → PhysicalWords.WordDistribution (n+1))
    (hRegulated : ∀ n, 0 < n → ∀ inputs (test : PhysicalWords.WordTest (n+1)),
      PhysicalWords.OrderedEuclideanTest test → Nonempty (RegulatedExpansion L
        (fun scale => F.running.coupling (RG.time scale))
        (fun scale => FilteredRG.strippedVacuumWord V F rotation scale n inputs test)
        (fun k => series k n inputs test))) :
    FilteredRG.AllOrderVacuumWordMatch V F rotation series := by
  intro n hn inputs test hTest
  obtain ⟨D⟩ := hRegulated n hn inputs test hTest
  exact D.continuum

end YMYMG.Existence
