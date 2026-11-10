/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import YangMills.OSRecon.Vendored.Axioms

/-!
# The linear growth conditions of Osterwalder–Schrader II

Osterwalder and Schrader, *Axioms for Euclidean Green's functions II*, Comm. Math. Phys. 42
(1975) 281–305, strengthen the temperedness axiom E0 by a growth condition on the orders of
the Schwinger distributions.  With the norms (their eq. (2.1))

  `|f|_p = sup_{x, |α| ≤ p} |(1 + x²)^{p/2} D^α f(x)|`

the two forms are, for constants `σ_n ≤ α (n!)^β`:

* **(E0'), eq. (4.1):** `𝔖₀ = 1` and `|𝔖_n(f)| ≤ σ_n |f|_{n·s}` for `f ∈ 𝒮₀(ℝ^{4n})`;
* **(E0''), eq. (4.2):** `|𝔖_n(f₁ × ⋯ × f_n)| ≤ σ_n ∏ |f_i|_s` on product test functions,

where `s` is fixed and independent of `n`.  Remarks 1–2 of OS II record that (E0'') implies
(E0') (with a different `s`), and that (E0') is what the reconstruction of tempered Wightman
distributions uses.

The formalization in `OSLinearGrowthCondition` (transcribed verbatim in `Vendored/Axioms.lean`)
departs from (4.1) in two ways: the norm index is `s` instead of `n·s`, and the norm is the
single Mathlib seminorm `sup ‖x‖^s ‖∂^s f‖` instead of the sup over `|α| ≤ p` with the weight
`(1 + x²)^{p/2}`.  As a consequence it cannot be satisfied by any theory whose zero-point
function is `1` (`GFF/GrowthCounterexample.lean`).  `OSArityLinearGrowthCondition` below is the corrected condition, and is now
upstream's public one: the package published on 2026-09-10 (branch
`codex/publish-os-proof-package-20260910`, commit `32b6102`) states it in
`OSReconstruction/Specification.lean`, where `OSLinearGrowthCondition` is an
abbreviation for it, and the two agree literally
(`scripts/check_vendored_osrecon.py`); the only difference of spelling is that
the published text factors the seminorm through the abbreviation
`osArityLinearSchwartzSeminorm d n s`.  The structures below state the two
conditions with the index `n·s` and the Mathlib family of seminorms
`(Finset.Iic (p, p)).sup (schwartzSeminormFamily ℝ E ℂ)`, which is equivalent to `|·|_p` up to
constants depending on `p` (and hence of at most factorial growth in `n` when `p = n·s`).
-/

open Finset

variable (d : ℕ) [NeZero d]

/-- **(E0'), OS II eq. (4.1).** `S₀ = 1` and `‖S_n(f)‖ ≤ α (n!)^β · ‖f‖_{n·s}`, with the
Schwartz norm of order `n·s`. -/
structure OSLinearGrowthCondition' (OS : OsterwalderSchraderAxioms d) where
  /-- Normalization at zero points: `S₀(f) = f(0)`. -/
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  /-- The order index `s`: the `n`-point function has order at most `n·s`. -/
  s : ℕ
  /-- The constants of the factorial bound `σ_n ≤ α (n!)^β`. -/
  alpha : ℝ
  beta : ℝ
  alpha_pos : 0 < alpha
  /-- The growth estimate (4.1). -/
  growth_estimate : ∀ (n : ℕ) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * (n.factorial : ℝ) ^ beta *
      (Finset.Iic (n * s, n * s)).sup (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1

/-- **(E0''), OS II eq. (4.2).** On product test functions `f₁ ⊗ ⋯ ⊗ f_n`,
`‖S_n(f₁ ⊗ ⋯ ⊗ f_n)‖ ≤ α (n!)^β ∏ ‖f_i‖_s` with a fixed order `s`. -/
structure OSProductGrowthCondition (OS : OsterwalderSchraderAxioms d) where
  /-- Normalization at zero points: `S₀(f) = f(0)`. -/
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  /-- The fixed order `s` of the one-point norms. -/
  s : ℕ
  /-- The constants of the factorial bound `σ_n ≤ α (n!)^β`. -/
  alpha : ℝ
  beta : ℝ
  alpha_pos : 0 < alpha
  /-- The growth estimate (4.2). -/
  growth_estimate : ∀ (n : ℕ) (f : Fin n → SchwartzSpacetime d) (F : ZeroDiagonalSchwartz d n),
    (∀ x, F.1 x = ∏ i, f i (x i)) →
    ‖OS.S n F‖ ≤ alpha * (n.factorial : ℝ) ^ beta *
      ∏ i, (Finset.Iic (s, s)).sup (schwartzSeminormFamily ℝ (SpacetimeDim d) ℂ) (f i)

/-! ### The corrected upstream form

The private corrected implementation of OSreconstruction (contract document
`OS_PUBLIC_CONTRACT_COMPARISON_2026-09-06.md`, §3) replaces the public
`OSLinearGrowthCondition` by `OSArityLinearGrowthCondition`, stated here literally: the same
seminorm family and index `n · s` as `OSLinearGrowthCondition'`, with the constant in the form
`α βⁿ (n!)^γ` instead of `α (n!)^β`.  The two are interchangeable, since `βⁿ ≤ e^β n!`, and the
conversions below make that a theorem in each direction.  A free-field instance is
`gffArityLinearGrowth` in `GFF/Growth.lean`. -/

/-- **`OSArityLinearGrowthCondition`**, the corrected upstream growth condition, verbatim in
its field list: `S₀(f) = f(0)`, and `‖Sₙ(f)‖ ≤ α βⁿ (n!)^γ · P_{n,s}(f)` with
`P_{n,s} = max_{k,l ≤ ns} p_{k,l}`. -/
structure OSArityLinearGrowthCondition (OS : OsterwalderSchraderAxioms d) where
  /-- Normalization at zero points: `S₀(f) = f(0)`. -/
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  /-- The per-arity growth rate of the seminorm index. -/
  sobolev_index : ℕ
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  /-- The bound, with index `n · s`. -/
  growth_estimate : ∀ (n : ℕ) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
      (Finset.Iic (n * sobolev_index, n * sobolev_index)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1

variable {d}

/-- OS II (4.1) is the upstream form with `β = 1`. -/
def OSLinearGrowthCondition'.toArity {OS : OsterwalderSchraderAxioms d}
    (G : OSLinearGrowthCondition' d OS) : OSArityLinearGrowthCondition d OS where
  normalized_zero := G.normalized_zero
  sobolev_index := G.s
  alpha := G.alpha
  beta := 1
  gamma := G.beta
  alpha_pos := G.alpha_pos
  beta_pos := one_pos
  growth_estimate := fun n f => by simpa using G.growth_estimate n f

/-- The upstream form is OS II (4.1) with `α ↦ α e^β` and `γ ↦ γ + 1`, since `βⁿ ≤ e^β n!`. -/
noncomputable def OSArityLinearGrowthCondition.toLinearGrowth' {OS : OsterwalderSchraderAxioms d}
    (G : OSArityLinearGrowthCondition d OS) : OSLinearGrowthCondition' d OS where
  normalized_zero := G.normalized_zero
  s := G.sobolev_index
  alpha := G.alpha * Real.exp G.beta
  beta := G.gamma + 1
  alpha_pos := mul_pos G.alpha_pos (Real.exp_pos _)
  growth_estimate := fun n f => by
    refine (G.growth_estimate n f).trans ?_
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hb : G.beta ^ n ≤ Real.exp G.beta * n.factorial := by
      have := Real.pow_div_factorial_le_exp G.beta G.beta_pos.le n
      rwa [div_le_iff₀ hfac] at this
    have hα : 0 ≤ G.alpha := G.alpha_pos.le
    have hN : 0 ≤ (Finset.Iic (n * G.sobolev_index, n * G.sobolev_index)).sup
        (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1 := apply_nonneg _ _
    have hg : 0 ≤ (n.factorial : ℝ) ^ G.gamma := Real.rpow_nonneg hfac.le _
    calc G.alpha * G.beta ^ n * (n.factorial : ℝ) ^ G.gamma *
          (Finset.Iic (n * G.sobolev_index, n * G.sobolev_index)).sup
            (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1
        ≤ G.alpha * (Real.exp G.beta * n.factorial) * (n.factorial : ℝ) ^ G.gamma *
          (Finset.Iic (n * G.sobolev_index, n * G.sobolev_index)).sup
            (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1 := by gcongr
      _ = G.alpha * Real.exp G.beta * (n.factorial : ℝ) ^ (G.gamma + 1) *
          (Finset.Iic (n * G.sobolev_index, n * G.sobolev_index)).sup
            (schwartzSeminormFamily ℝ (NPointDomain d n) ℂ) f.1 := by
          rw [Real.rpow_add hfac, Real.rpow_one]
          ring

