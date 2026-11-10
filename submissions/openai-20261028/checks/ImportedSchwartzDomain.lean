import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section
open scoped SchwartzMap
namespace SchwartzMap

/-- A domain equivalence acts continuously and complex linearly by pullback. -/
def complexDomCongr {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : D ≃L[ℝ] E) :
    𝓢(E, ℂ) ≃L[ℂ] 𝓢(D, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLMOfContinuousLinearEquiv ℂ g)
    (compCLMOfContinuousLinearEquiv ℂ g.symm)
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.apply_symm_apply x))
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.symm_apply_apply x))

@[simp] theorem complexDomCongr_apply {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : D ≃L[ℝ] E)
    (f : 𝓢(E, ℂ)) (x : D) : complexDomCongr g f x = f (g x) := rfl

end SchwartzMap
