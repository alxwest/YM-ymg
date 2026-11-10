import OPESpec

/-! Reference statement only. The solution is OPECheck.lean. -/
set_option autoImplicit false
namespace YMReview.OPE
open YangMills

theorem constructed (g : GaugeGroup) (hg : g.IsSimple) :
    ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ CommonOPE T := by
  sorry

end YMReview.OPE
