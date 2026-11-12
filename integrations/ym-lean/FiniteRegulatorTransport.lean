import YM.PertExtension.Normalized
import YangMills.RenormalizationGroup

set_option autoImplicit false
set_option warningAsError true

/-!
# Actual finite-regulator expectations in the native jet predicate

The source's `Aspiration` bounds each order-N remainder by C g^(N+1).
This implies ym-lean's epsilon g^N formulation. Apply that implication to
the source's actual normalized Wilson expectations and its prescribed
finite-regulator coefficients, including the version before tree reduction.

The cutoff stays fixed throughout these theorems. No continuum limit,
renormalized coupling substitution, coefficient identification with the
native fixed flow, or selected-vacuum word matching is asserted here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace YMYMG.FiniteRegulatorTransport

open YM.PertExtension.Series YM.PertExtension.Series.Tested

theorem aspiration_has_jet {f : ℝ → ℝ} {a : ℕ → ℝ}
    (h : Aspiration f a) :
    YangMills.RG.HasPerturbativeJet (fun g => (f g : ℂ))
      (fun k => (a k : ℂ)) := by
  intro N epsilon hEpsilon
  obtain ⟨C, hC, hBound⟩ := h N
  have hSmall : ∀ᶠ g : ℝ in 𝓝[>] 0, g < epsilon / (C + 1) :=
    eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (show 0 < epsilon / (C + 1) by positivity))
  obtain ⟨delta, hDelta, hBoth⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (hBound.and hSmall)
  refine ⟨delta, hDelta, fun g hG hGDelta => ?_⟩
  obtain ⟨hRem, hScale⟩ := hBoth ⟨hG, hGDelta⟩
  have hCG : C * g ≤ epsilon := by
    have h := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hScale
    nlinarith
  have hSum : (∑ k ∈ Finset.range (N + 1), (g : ℂ) ^ k * (a k : ℂ)) =
      ((peval a N g : ℝ) : ℂ) := by
    simp [peval, Zone.eval, smul_eq_mul]
  calc
    ‖(f g : ℂ) - ∑ k ∈ Finset.range (N + 1), (g : ℂ) ^ k * (a k : ℂ)‖ =
        ‖f g - peval a N g‖ := by
      rw [hSum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C * g ^ (N + 1) := hRem
    _ = (C * g) * g ^ N := by rw [pow_succ]; ring
    _ ≤ epsilon * g ^ N := mul_le_mul_of_nonneg_right hCG (pow_nonneg hG.le N)

open YM YM.Lattice YM.Wilson YM.PertExtension.Orb

theorem finite_wilson_jet {G : Gauge} {n : Side} {O : Observable G n}
    (even : Even n.val) (h : LocalTest O) :
    YangMills.RG.HasPerturbativeJet (fun g => (expectation O g : ℂ))
      (fun k => (diag O k : ℂ)) :=
  aspiration_has_jet (finite_formula even (traySpec G) h)

theorem finite_haar_wilson_jet {G : Gauge} {n : Side} {O : Config G n → ℝ}
    (even : Even n.val) (h : PreTest O) :
    YangMills.RG.HasPerturbativeJet (fun g => (preExpectation O g : ℂ))
      (fun k => (diag (restrictedO O) k : ℂ)) :=
  aspiration_has_jet (before_tree_formula even (traySpec G) h)

end YMYMG.FiniteRegulatorTransport
