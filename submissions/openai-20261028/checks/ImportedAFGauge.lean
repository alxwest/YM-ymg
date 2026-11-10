/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gauge group data for the Yang-Mills problem

The Clay Millennium Prize problem (Jaffe-Witten) asks for quantum Yang-Mills
theory on `ℝ⁴` with any *compact simple* gauge group `G`.

At the level of the problem *statement*, the gauge group enters through:

1. **The construction side** (which theory one builds): lattice Yang-Mills with
   structure group `G`, its continuum limit — this lives in the Reduction layer
   and, eventually, in a dependency on the `lgt` project.
2. **The identification side** (why the constructed theory *is* Yang-Mills):
   the short-distance behavior of correlation functions of gauge-invariant
   operators such as `tr F²` must be asymptotically approximated by
   renormalized perturbation theory.  The perturbative coefficients depend on
   `G` only through Lie-algebra invariants: the dimension `dim G` (number of
   gluon species) and the quadratic Casimir of the adjoint representation
   (equivalently the dual Coxeter number `h∨`), which fixes the one-loop beta
   function.

This file records exactly that invariant data, as a lightweight structure.
Tying it to an actual compact simple Lie group from Mathlib
(`Matrix.specialUnitaryGroup`, and eventually the general classification) is a
roadmap item (see `docs/roadmap.md`, milestone M4); nothing in the statement
layer depends on the group beyond these invariants yet.

## Conventions

The one-loop beta function is written
`μ d g/d μ = − b₀ g³ / (16 π²) + O(g⁵)` with `b₀ = (11/3) C₂(adj)`, and the
adjoint Casimir is normalized so that `C₂(adj) = n` for `G = SU(n)` with the
standard normalization `tr (T^a T^b) = ½ δ^{ab}` in the fundamental — which
for `SU(n)` coincides with the dual Coxeter number, `C₂(adj) = h∨ = n`.  (The
relation `C₂(adj) = 2 h∨` belongs to the root normalization `θ² = 2`, not to
this one; an earlier version of this docstring wrote `C₂(adj) = 2 h∨ = n`,
which is inconsistent since `2h∨ = 2n`.)
Hence `b₀ = 11 n / 3` for `SU(n)`.
-/

/-- The Lie-algebra invariants of a compact simple gauge group that appear in
the statement of the Yang-Mills existence and mass gap problem: the dimension
of the Lie algebra and the quadratic Casimir of the adjoint representation.

For `SU(n)`: `dimG = n² − 1`, `casimirAdj = n`. -/
structure GaugeGroupData where
  /-- Dimension of the Lie algebra of `G` (the number of gluon species). -/
  dimG : ℕ
  /-- Quadratic Casimir `C₂(adj)` of the adjoint representation, in the
  normalization where `C₂(adj) = n` for `SU(n)` (equivalently, the dual
  Coxeter number `h∨` in the `b = 1` normalization of
  van Ritbergen-Vermaseren-Larin). -/
  casimirAdj : ℝ
  /-- The dimensionless adjoint quartic-Casimir ratio
  `d̂₄ = (d_A^{abcd}d_A^{abcd}/N_A)/C₂(adj)⁴`, with
  `d_A^{abcd} = (1/4!)·Σ_perms Tr_adj(T^aT^bT^cT^d)` (no trace
  subtraction).  Independent of generator normalization.  Values from
  van Ritbergen-Schellekens-Vermaseren [hep-ph/9802376], independently
  verified by direct numerical contraction: `(n²+36)/(24n²)` for
  `SU(n)`; `139/1500` for `so(7)`; `235/1536` for `sp(6)`; `145/3993`
  for `so(13)`; `25/(12(N_A+2))` for the exceptionals (e.g. `5/192` for
  `e₆`).  This is the first group invariant beyond `dim G` visible in
  UV data (via the four-loop beta function), and it separates the
  dimension-coincident pairs. -/
  quarticRatio : ℝ
  /-- The group is nontrivial. -/
  dimG_pos : 0 < dimG
  /-- The adjoint Casimir is positive (true for any compact simple `G`). -/
  casimirAdj_pos : 0 < casimirAdj
  /-- The quartic ratio is positive (a contraction of squares). -/
  quarticRatio_pos : 0 < quarticRatio

namespace GaugeGroupData

/-- The one-loop beta-function coefficient `b₀ = (11/3) C₂(adj)`, in the
convention `μ dg/dμ = − b₀ g³/(16π²)`.  Its positivity — asymptotic freedom of
perturbative Yang-Mills — is what makes the short-distance identification
criterion (`YangMills.Core.ShortDistance`) possible. -/
noncomputable def betaZero (G : GaugeGroupData) : ℝ :=
  11 / 3 * G.casimirAdj

theorem betaZero_pos (G : GaugeGroupData) : 0 < G.betaZero := by
  have := G.casimirAdj_pos
  unfold betaZero
  positivity

/-- The two-loop beta-function coefficient `b₁ = (34/3) C₂(adj)²`, in the
convention `μ dg/dμ = − b₀ g³/(16π²) − b₁ g⁵/(16π²)²`.  For `SU(3)`:
`b₁ = 102`. -/
noncomputable def betaOne (G : GaugeGroupData) : ℝ :=
  34 / 3 * G.casimirAdj ^ 2

theorem betaOne_pos (G : GaugeGroupData) : 0 < G.betaOne := by
  have := G.casimirAdj_pos
  unfold betaOne
  positivity

/-- **Universality of the two-loop ratio in pure Yang-Mills.**  Because
`b₀ ∝ C₂(adj)` and `b₁ ∝ C₂(adj)²`, the scheme-independent ratio `b₁/b₀²`
equals `102/121` for *every* compact simple gauge group.  Consequently the
first two orders of the short-distance asymptotics of the `tr F²` two-point
function (see `YangMills.Core.ShortDistance`) do not distinguish gauge
groups: the identification of `G` must come from the constructive side
(lattice regularization with structure group `G`) or from multi-operator
data — see `docs/roadmap.md`, milestone M4. -/
theorem betaOne_div_betaZero_sq (G : GaugeGroupData) :
    G.betaOne / G.betaZero ^ 2 = 102 / 121 := by
  have hc : G.casimirAdj ≠ 0 := ne_of_gt G.casimirAdj_pos
  unfold betaOne betaZero
  field_simp
  ring

/-- The invariant data of `SU(n)`, `n ≥ 2`: `dim = n² − 1`,
`C₂(adj) = n`, `d̂₄ = (n²+36)/(24n²)` (VSV, verified numerically for
`n = 2, 3, 4`: `5/12`, `5/24`, `13/96`). -/
noncomputable def su (n : ℕ) (hn : 2 ≤ n) : GaugeGroupData where
  dimG := n ^ 2 - 1
  casimirAdj := n
  quarticRatio := ((n : ℝ) ^ 2 + 36) / (24 * (n : ℝ) ^ 2)
  dimG_pos := by
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    omega
  casimirAdj_pos := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hn
  quarticRatio_pos := by
    have hn0 : (0 : ℝ) < (n : ℝ) :=
      by exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hn
    positivity

/-- For `SU(3)` (quantum chromodynamics without quarks): `b₀ = 11`. -/
example : (su 3 (by norm_num)).betaZero = 11 := by
  norm_num [su, betaZero]

end GaugeGroupData
