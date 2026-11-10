/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import YangMills.OSRecon.Vendored.OSConj

/-!
# Vendored from OSreconstruction: the Osterwalder–Schrader axioms

Upstream: https://github.com/xiyin137/OSreconstruction, local fork
`cherkis/OSreconstruction` at commit `936defd39f199b38301c05e8caeae6b16eb7d167`.

Source: `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean` 29-34
(`OSInnerProduct`), 66-68 (`OSTensorAdmissible`), 211-220
(`OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion`), 706-820
(`OsterwalderSchraderAxioms`, `schwingerCLM`), 1805-1839 (`OSLinearGrowthCondition`).

Deviations: none in the declarations. `OSLinearGrowthCondition` is transcribed
verbatim so that it can be refuted for the free field
(`YangMills/OSRecon/GFF/GrowthCounterexample.lean`); the corrected conditions
following Osterwalder–Schrader II are in `YangMills/OSRecon/Growth.lean`.

That refutation is now upstream's position too.  In the package published on
2026-09-10 (branch `codex/publish-os-proof-package-20260910`, commit
`32b6102`) this condition is renamed `OSFixedOrderGrowthCondition` and moved to
`Wightman/Reconstruction/WickRotation/deprecated/`, with
`OSFixedOrderGrowthCondition.sobolev_index_eq_zero` — the normalization forces
its Schwartz order to be zero — and the public name `OSLinearGrowthCondition`
is now an abbreviation for the arity-linear condition.  The name is kept here
for the counterexample, which is about the condition as it was published at
`135ed13`.  `OsterwalderSchraderAxioms` and `OSInnerProduct` are unchanged by
the correction and agree with the published text
(`scripts/check_vendored_osrecon.py`).
-/

noncomputable section

open scoped SchwartzMap
open Topology

variable (d : ℕ) [NeZero d]

set_option linter.unusedSectionVars false

def OSInnerProduct (S : SchwingerFunctions d) (F G : BorchersSequence d) : ℂ :=
  ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1),
      S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct (G.funcs m)))

/-- The genuine zero-diagonal compatibility condition for the OS tensor terms
    appearing in `OSInnerProduct`.

    This is the precise hypothesis needed for additive manipulations on the
    Euclidean side after the hard cut to `ZeroDiagonalSchwartz`. -/
def OSTensorAdmissible (F G : BorchersSequence d) : Prop :=
  ∀ n m, VanishesToInfiniteOrderOnCoincidence
    ((F.funcs n).osConjTensorProduct (G.funcs m))

/-- Ordered positive-time topological support is enough to guarantee that every
    OS tensor term of two Borchers sequences already lies in `°S`. -/
theorem OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
    (F G : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG : ∀ n, tsupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    OSTensorAdmissible d F G := by
  intro n m
  exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    (d := d) (f := F.funcs n) (g := G.funcs m) (hF n) (hG m)

/-- The Osterwalder-Schrader axioms E0-E4 for Euclidean field theory.

    From OS I (1973):
    - E0: Temperedness (Sₙ ∈ S'(ℝ^{dn}))
    - E1: Euclidean invariance
    - E2: Reflection positivity: Σₙ,ₘ Sₙ₊ₘ(Θf* × fₘ) ≥ 0 for f ∈ S₊
    - E3: Symmetry: Sₙ(f) = Sₙ(f^π) for all permutations π
    - E4: Cluster property

    **Important**: As shown in OS II (1975), these axioms alone may NOT be
    sufficient to reconstruct a Wightman QFT. The linear growth condition E0'
    is needed. See `OSLinearGrowthCondition`.

    **Critical correction**: the heart of OS reconstruction is precisely the
    passage from Euclidean data defined only on the zero-diagonal test space
    `°S` to full tempered Wightman distributions on Schwartz space. The Euclidean
    starting point must therefore be stated on `ZeroDiagonalSchwartz` itself,
    not on a fictitious full-Schwartz Schwinger theory. -/
structure OsterwalderSchraderAxioms (d : ℕ) [NeZero d] where
  /-- The honest zero-diagonal Euclidean Schwinger family. -/
  S : SchwingerFunctions d
  /-- E0: Temperedness on the OS-I zero-diagonal test space `°S`.

      The literal OS-I Schwinger functions are distributions on the coincidence-free
      test space, not a priori on the full Schwartz space. Any later extension to
      all of `SchwartzNPoint` is extra structure beyond this axiom surface.

      The point is that inverse-power coincidence singularities are compatible
      with `°S`: zero-diagonal test functions vanish to arbitrarily high order on
      the coincidence locus, so kernels of finite singular order still define the
      honest Euclidean pairing there. This is why the corrected OS axiom is stated
      on `ZeroDiagonalSchwartz`, not on full Schwartz space. -/
  E0_tempered : ∀ n, Continuous (S n)
  /-- E0 also includes linearity on the honest Euclidean test space `°S`. -/
  E0_linear : ∀ n, IsLinearMap ℂ (S n)
  /-- E0 also includes the Schwinger reality condition induced by Wightman
      Hermiticity:
      `conj (S_n(f)) = S_n(f.osConj)`.

      The transformed test function is supplied as a zero-diagonal witness rather
      than by asserting a full-Schwartz Euclidean theory. -/
  E0_reality : ∀ (n : ℕ) (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
    starRingEnd ℂ (S n f) = S n g
  /-- E1a: Translation invariance.
      S_n(x₁+a,...,xₙ+a) = S_n(x₁,...,xₙ) for all a ∈ ℝ^{d+1}. -/
  E1_translation_invariant : ∀ (n : ℕ) (a : SpacetimeDim d)
    (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => x i + a)) →
    S n f = S n g
  /-- E1b: Rotation invariance under SO(d+1).
      S_n(Rx₁,...,Rxₙ) = S_n(x₁,...,xₙ) for all R ∈ SO(d+1).
      Together with E1a, this gives Euclidean covariance under ℝ^{d+1} ⋊ SO(d+1).
      Note: Full O(d+1) invariance (including improper rotations with det=-1)
      would require parity invariance, which is not implied by the Wightman axioms. -/
  E1_rotation_invariant : ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    R.transpose * R = 1 → R.det = 1 →
    ∀ (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
    S n f = S n g
  /-- E2: Reflection positivity - the crucial axiom for Hilbert space construction.
      For test functions whose topological support lies in the OS-I ordered positive-time region
      `0 < x₁⁰ < ... < xₙ⁰`,
      `Σₙ,ₘ S_{n+m}(θf̄ₙ ⊗ fₘ) ≥ 0`
      where θ is time reflection θ(τ,x⃗) = (-τ,x⃗) and f̄ is complex conjugation.
      This uses `OSInnerProduct` (time reflection + conjugation), the correct
      inner product for the Euclidean framework.
      This ensures the reconstructed inner product is positive definite. -/
  E2_reflection_positive : ∀ (F : BorchersSequence d),
    (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) →
    (OSInnerProduct d S F F).re ≥ 0
  /-- E3: Permutation symmetry - Schwinger functions are symmetric under
      permutation of arguments: S_n(x_{σ(1)},...,x_{σ(n)}) = S_n(x₁,...,xₙ)
      for all permutations σ ∈ Sₙ. -/
  E3_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
    S n f = S n g
  /-- E4: Cluster property - factorization at large separations.
      lim_{|a|→∞} S_{n+m}(x₁,...,xₙ,y₁+a,...,yₘ+a) = S_n(x₁,...,xₙ) · S_m(y₁,...,yₘ)
      This reflects the uniqueness of the vacuum in the reconstructed theory.

      Expressed via the connected n-point functions: the connected part Sₙᶜ vanishes
      for n ≥ 2 at large separations. Equivalently, for product test functions
      with widely separated supports, S_{n+m} factorizes. -/
  E4_cluster : ∀ (n m : ℕ) (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m),
    -- Cluster property: as spatial separation increases, S_{n+m} factorizes.
    -- For any ε > 0, there exists R > 0 such that for spatial translation a with |a| > R,
    -- |S_{n+m}(f ⊗ τ_a g) - S_n(f) · S_m(g)| < ε
    -- where τ_a g is g translated by a in all m coordinates.
    -- The translation a must be purely spatial (a 0 = 0): Euclidean time shifts
    -- correspond to imaginary Minkowski time, leaving the cluster property's domain.
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        -- For any Schwartz function g_a that is the translation of g by a:
        ∀ (g_a : ZeroDiagonalSchwartz d m),
          (∀ x : NPointDomain d m, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + m)),
            (∀ x : NPointDomain d (n + m),
              fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
            ‖S (n + m) fg_a - S n f * S m g‖ < ε

/-- The Schwinger functional packaged as a continuous linear map on the honest
zero-diagonal test space. -/
def OsterwalderSchraderAxioms.schwingerCLM
    (OS : OsterwalderSchraderAxioms d) (n : ℕ) :
    ZeroDiagonalSchwartz d n →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := OS.S n
      map_add' := (OS.E0_linear n).map_add
      map_smul' := (OS.E0_linear n).map_smul }
  cont := OS.E0_tempered n

/-- The linear growth condition E0' from OS II (1975).

    This replaces the simple temperedness E0 with a stronger condition:
    There exist s ∈ ℤ₊ and constants α, β, γ such that for σₙ ≤ αβⁿ(n!)^γ,
      |Sₙ(f)| ≤ σₙ ‖f‖_{s,n}

    This condition controls the growth of the distribution order as n → ∞,
    which is essential for proving temperedness of the reconstructed
    Wightman distributions.

    The key point is that this growth hypothesis belongs on the Euclidean side
    before reconstruction; it does not erase the main difficulty. The theorem
    still has to manufacture full tempered Wightman distributions starting only
    from Schwinger data whose honest Euclidean test space is `°S`. -/
structure OSLinearGrowthCondition (d : ℕ) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  /-- E0' normalization at zero points: `S₀(f) = f(0)`. -/
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  /-- The Sobolev index s -/
  sobolev_index : ℕ
  /-- Factorial growth bound constants: σₙ ≤ α · βⁿ · (n!)^γ -/
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  /-- The bounds are positive -/
  alpha_pos : alpha > 0
  beta_pos : beta > 0
  /-- The linear growth estimate: |Sₙ(f)| ≤ σₙ · ‖f‖_{s,n}
      where σₙ ≤ α · βⁿ · (n!)^γ bounds the distribution order growth,
      and ‖f‖_{s,n} is the Schwartz seminorm of order s on n-point functions.

      This is equation (4.1) of OS II: |Sₙ(f)| ≤ σₙ |f|_s
      where |f|_s = SchwartzMap.seminorm ℝ s s (f). -/
  growth_estimate : ∀ (n : ℕ) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
      SchwartzMap.seminorm ℝ sobolev_index sobolev_index f.1

end
