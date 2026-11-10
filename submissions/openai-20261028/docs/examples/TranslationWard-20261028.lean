import WardFormulationAudit

/-!
# [A6] The normalized translation Ward identity — 28 October 2026

An abstract conserved tensor is not enough to identify the stress tensor's
normalization: it must act on other fields as the generator of translations.
This walkthrough displays that action, including the sign, coefficient,
integrability and allowed smearing geometry. It uses the existing
`WardFormulationAudit` results included in the combined acceptance theorem.

`F.sector.energy a b` is the tensor field of the fixed construction F. The
same tensor occurs for every central field, spectator word and character
phase; no coefficient is fitted separately for each correlation function.
-/

set_option autoImplicit false
noncomputable section
namespace YMReview.Examples.TranslationWard
open YM YM.Table Set MeasureTheory
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {o : Extraction.Order}
variable {S : Table C.book} (F : Spec.Final C o S)

/-!
## 1. An admissible shell really exists

The configuration x contains the central insertion x 0 and n spectator
positions x i.succ. `hx` says that these points are distinct. `Window x χ`
means that χ is smooth and compactly supported, equals one near x 0, and
has support avoiding every spectator. Its derivative is supported away from
all those insertions. This is the smooth-cutoff version of a surrounding
surface integral.

The existence lemma prevents the Ward statement from being vacuous through
an impossible choice of shell. Its size can depend on the separated
configuration; no common shell is asserted as points collide.
-/

theorem admissible_shell_exists {n : ℕ} (x : Points (n + 1))
    (hx : x ∈ conf (n + 1)) : ∃ χ : E4 → ℝ, Window x χ :=
  WardAudit.windows_exist x hx

/-!
## 2. Identify the right-hand side with a coordinate derivative

In physics notation the next theorem is

  - sum_a integral dy (partial_a χ)(y)
      <T_ab(y) B(x_0) spectators>_i
    = partial_(x_0)^b <B(x_0) spectators>_i.

`B : S.Field d` is any quotient field of any degree d; `q` is any finite
list of spectator fields, whose degrees may differ. `i` is any character
phase. The order and coefficient on the right are explicit.

Two source conclusions are composed in the proof. The shell law first gives
the insertion of the abstract field derivative. The calculus law identifies
that insertion with the ordinary derivative of the correlation kernel in
the central coordinate. Reading only the former would miss a necessary
part of the normalization check.
-/

theorem tensor_generates_translations (i : F.α.space.X) {n d : ℕ}
    {x : Points (n + 1)} (hx : x ∈ conf (n + 1)) (q : Fin n → S.Tag)
    {χ : E4 → ℝ} (hχ : Window x χ) (b : Axis) (B : S.Field d) :
    - ∑ a : Axis, ∫ y : E4,
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q)) =
      Points.gradient 0 b
        (fun z => S.useAt (F.α.ensemble i) z (Fin.cons ⟨d, B⟩ q)) x := by
  exact ((F.phase.phase.flux i).translation hx q hχ b d B).trans
    ((F.phase.phase.calculus i).kernels d b B hx q)

/-!
## 3. The integral is an actual integral

The derivative of χ removes the potentially singular regions at the
insertions. Smoothness at separated configurations and compact support then
give integrability. Stating this separately rules out relying on the
totalized value that Lean assigns to an integral of a nonintegrable function.
-/

theorem shell_integrand_is_integrable (i : F.α.space.X) {n d : ℕ}
    {x : Points (n + 1)} (hx : x ∈ conf (n + 1)) (q : Fin n → S.Tag)
    {χ : E4 → ℝ} (hχ : Window x χ) (a b : Axis) (B : S.Field d) :
    Integrable (fun y : E4 =>
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q))) :=
  WardAudit.phase_translation_integrable F i hx q hχ a b B

/-!
## 4. Independence of the surrounding window

Both windows produce the same field derivative, so their shell charges
agree. The field, positions, phase and tensor are kept fixed. This is not
an assertion of independence from a regulator while changing the theory.
-/

theorem shell_charge_is_window_independent (i : F.α.space.X) {n d : ℕ}
    {x : Points (n + 1)} (hx : x ∈ conf (n + 1)) (q : Fin n → S.Tag)
    {χ ψ : E4 → ℝ} (hχ : Window x χ) (hψ : Window x ψ)
    (b : Axis) (B : S.Field d) :
    shellGrad (F.α.ensemble i) F.sector.energy χ b x q B =
      shellGrad (F.α.ensemble i) F.sector.energy ψ b x q B :=
  WardAudit.phase_window_independent F i hx q hχ hψ b B

/-!
## What has and has not been normalized

This fixes the translation action relative to the construction's Euclidean
coordinate and derivative conventions. It provides a more specific check
than conservation or the trace two-point function alone. It is not a proof
that all possible stress-tensor improvements vanish: an improvement may
leave the translation charge unchanged.

The formula is a separated-insertion shell identity. It does not construct
an unrestricted contact-term extension, a dilation Ward identity, or a
comparison with an independently chosen Minkowski sign convention. Those
questions should not be silently included in what [A6] claims to check.
-/

#print axioms admissible_shell_exists
#print axioms tensor_generates_translations
#print axioms shell_integrand_is_integrable
#print axioms shell_charge_is_window_independent
end YMReview.Examples.TranslationWard
