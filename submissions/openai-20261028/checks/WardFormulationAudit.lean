import YM.Spec.Closed
import YM.Work.A01.Support

/-! Checks of the submitted shell formulation, with the translation right-hand
side stated as an ordinary coordinate derivative. These are consequences of
one submitted Final; they do not supply contact extensions or fix an external
Euclidean/Minkowski sign convention. -/

set_option autoImplicit false
noncomputable section
namespace YMReview.WardAudit
open YM YM.Table Set MeasureTheory
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {o : Extraction.Order}
variable {S : Table C.book} (F : Spec.Final C o S)

/-- Every separated configuration admits an admissible shell. -/
theorem windows_exist {n : ℕ} (x : Points (n+1)) (hx : x ∈ conf (n+1)) :
    ∃ χ : E4 → ℝ, Window x χ :=
  YM.Work.A01.exists_window x hx

/-- The same stress field generates the actual coordinate derivative in every
phase, for every central field and every finite list of exterior spectators. -/
theorem phase_translation_derivative (i : F.α.space.X) {n d : ℕ}
    {x : Points (n+1)} (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag)
    {χ : E4 → ℝ} (hχ : Window x χ) (b : Axis) (B : S.Field d) :
    - ∑ a : Axis, ∫ y : E4,
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q)) =
      Points.gradient 0 b
        (fun z => S.useAt (F.α.ensemble i) z (Fin.cons ⟨d, B⟩ q)) x := by
  exact ((F.phase.phase.flux i).translation hx q hχ b d B).trans
    ((F.phase.phase.calculus i).kernels d b B hx q)

/-- Shell integrability is proved, rather than relying on the totalized value
of a Lean integral for a nonintegrable function. -/
theorem phase_translation_integrable (i : F.α.space.X) {n d : ℕ}
    {x : Points (n+1)} (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag)
    {χ : E4 → ℝ} (hχ : Window x χ) (a b : Axis) (B : S.Field d) :
    Integrable (fun y : E4 =>
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q))) := by
  simpa only [mul_one] using
    (Table.integrableShell hx hχ (F.phase.phase.states i).smooth
      (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q))
      a (fun _ => (1 : ℂ)) continuous_const)

/-- Two admissible windows give the same charge, with the state and fields
held fixed. -/
theorem phase_window_independent (i : F.α.space.X) {n d : ℕ}
    {x : Points (n+1)} (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag)
    {χ ψ : E4 → ℝ} (hχ : Window x χ) (hψ : Window x ψ)
    (b : Axis) (B : S.Field d) :
    shellGrad (F.α.ensemble i) F.sector.energy χ b x q B =
      shellGrad (F.α.ensemble i) F.sector.energy ψ b x q B := by
  exact ((F.phase.phase.flux i).translation hx q hχ b d B).trans
    ((F.phase.phase.flux i).translation hx q hψ b d B).symm

end YMReview.WardAudit

#print axioms YMReview.WardAudit.windows_exist
#print axioms YMReview.WardAudit.phase_translation_derivative
#print axioms YMReview.WardAudit.phase_translation_integrable
#print axioms YMReview.WardAudit.phase_window_independent
