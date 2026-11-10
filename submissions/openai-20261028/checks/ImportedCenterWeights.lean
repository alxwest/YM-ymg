import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
/-! Exact excerpts from yang-mills DifferentiatedKernels.lean; see provenance.json. -/
noncomputable section
open MeasureTheory
namespace EuclideanField
variable {E : Type*} [NormedAddCommGroup E]
/-- Integrable polynomial center weight. -/
def centerWeight (q : ℕ) (y : E) : ℝ := ((1 + ‖y‖) ^ q)⁻¹

lemma centerWeight_nonneg (q : ℕ) (y : E) : 0 ≤ centerWeight q y := by
  unfold centerWeight
  positivity

lemma centerWeight_pos (q : ℕ) (y : E) : 0 < centerWeight q y := by
  unfold centerWeight
  positivity

variable [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E] [SigmaFinite (volume : Measure E)]

omit [SecondCountableTopology E] [SigmaFinite (volume : Measure E)] in
lemma integrable_centerWeight [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (q : ℕ) (hq : Module.finrank ℝ E < q) :
    Integrable (centerWeight q : E → ℝ) := by
  have heq : (centerWeight q : E → ℝ) = fun x : E => (1 + ‖x‖) ^ (-(q : ℝ)) := by
    funext x
    simp [centerWeight]
  rw [heq]
  exact (integrable_one_add_norm (E := E) (μ := volume) (by exact_mod_cast hq :
      (Module.finrank ℝ E : ℝ) < (q : ℝ)))

end EuclideanField
