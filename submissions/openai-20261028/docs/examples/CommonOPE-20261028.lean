-- SPDX-License-Identifier: Apache-2.0
import OPECheck

/-!
# [A8] What the common OPE check proves — 28 October 2026

The OPE check is more than the bare assertion that some expansion exists.
It exposes bounds on coefficients and on finite-truncation remainders, with
the same coefficients in the mixed hierarchy and every character phase.
This walkthrough uses `OPESpec` and `OPECheck`, the unchanged separate OPE
review target and proof. The A-labels refer to the current assessment draft.

`T : Hierarchy C` contains fields, correlations and coefficients. A field tag
`a k` includes its filtration degree `(a k).1`; this is not a declaration of
an exact interacting scaling dimension. `T.Channel j` is the finite channel
set at degree j, and `T.actor j i` is its field. The coefficients already
belong to T before a phase, spectators or a truncation order are requested.
-/

set_option autoImplicit false
noncomputable section
namespace YMReview.Examples.CommonOPE
open YangMills YangMills.Hierarchy Function Set Filter
open scoped Topology BigOperators Classical
variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

/-!
## 1. Turn filter notation into a radius statement

The source states small-distance bounds using “eventually as r tends to zero
from above.” The adapter replaces this with a positive radius ρ and a bound
for every 0 < r < ρ. It retains the source estimates; it does not rederive
them analytically. `CommonOPE` itself states the estimates without referring
to the source `OperatorProductExpansion` predicate.
-/

theorem explicit_radius_from_source (h : T.OperatorProductExpansion) :
    OPE.CommonOPE T := OPE.from_source h

/-!
## 2. Bounds on the actual coefficient functions

`Cluster r M η x o` says that all cluster points lie within M r of the
expansion center o and are mutually separated by at least η r. Thus the
cluster shrinks while its relative shape stays away from additional
collisions. The coefficient bound is uniform over all such positions.

For input degrees d_k and output degree j, the exponent is
`j - sum_k d_k - ε`. The arbitrarily small positive loss ε accommodates
behavior such as logarithms. The apparent prefactor one is achieved by
shrinking ρ; this is an asymptotic bound, not an explicit numerical value
of ρ or a calculation of a perturbative coefficient.
-/

theorem coefficient_bound (h : OPE.CommonOPE T) {n : ℕ}
    (a : Fin n → T.Tag) (j : ℕ) (i : T.Channel j) (M η ε : ℝ)
    (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ∀ x o, OPE.Cluster r M η x o →
        ‖T.coefficient a j i x o‖ ≤
          r ^ ((j : ℝ) - (∑ k, ((a k).1 : ℝ)) - ε) :=
  h.coefficient_radius a j i M η ε hM hη hε

/-!
## 3. A remainder uniform in phases and separated spectators

`Spectators c y o` keeps all spectator points at least c from the center and
from one another. The truncated expression sums channels through degree D:
each coefficient multiplies the correlation with the cluster replaced by
that channel's field at o, retaining all spectators in the same state.

The state parameter `s : Option T.Character` uses `none` for the mixed
hierarchy and `some i` for a character phase. In the theorem below ρ is
chosen BEFORE s and all allowed positions. It can depend on the field
labels, D and the geometric constants, but not on the requested phase.
This is the substantive uniformity exposed by the review target.
-/

theorem remainder_uniform_in_state (h : OPE.CommonOPE T) {n m : ℕ}
    (a : Fin n → T.Tag) (b : Fin m → T.Tag) (D : ℕ) (M η c ε : ℝ)
    (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ∀ (s : Option T.Character) x o y,
        OPE.Cluster r M η x o → OPE.Spectators c y o →
          ‖T.grouped s a x b y - OPE.truncated T s a x b y o D‖ ≤
            r ^ ((D : ℝ) + 1 - (∑ k, ((a k).1 : ℝ)) - ε) :=
  h.remainder_radius a b D M η c ε hM hη hc hε

/-!
## 4. Common coefficients do not force equal phases

Subtract the two expansions. The coefficients remain the same, while the
correlations of the output fields with spectators can differ between states.
The triangle inequality gives twice the original remainder, at the same
radius. This explains how phase dependence can survive even with a common
short-distance OPE.
-/

theorem difference_of_states (h : OPE.CommonOPE T) {n m : ℕ}
    (a : Fin n → T.Tag) (b : Fin m → T.Tag) (D : ℕ) (M η c ε : ℝ)
    (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ∀ (s t : Option T.Character) x o y,
        OPE.Cluster r M η x o → OPE.Spectators c y o →
          ‖(T.grouped s a x b y - T.grouped t a x b y) -
            ∑ j : Fin (D + 1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
              (T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y -
               T.grouped t (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y)‖ ≤
          2 * r ^ ((D : ℝ) + 1 - (∑ k, ((a k).1 : ℝ)) - ε) :=
  OPE.phase_difference h a b D M η c ε hM hη hc hε

/-!
## 5. Channels refer to the source's fields

At the source level, `Reader` supplies the field-valued coefficient and its
channel coordinates. `channel_assembly` checks that summing those coordinates
recovers that field. `single_insertion_recovered` checks the normalization
of the one-insertion expansion once its degree is included. These are useful
dictionary checks, not computations of interacting multi-insertion OPE values.
-/

section FieldDictionary
open YM YM.Table YM.OPE.Orbits
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
    (F : Spec.Final C o S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem channel_assembly {I : Type} [Fintype I] {d : I → ℕ}
    (a : Labels S d) (x : I → E4) (z : E4) (j : ℕ) :
    ∑ i : Q.channels j, Q.coef j i x a z • Q.actor j i = Q.fresh j x z a :=
  YMReview.OPE.channel_assembly F Q a x z j

theorem single_insertion_recovered (D j : ℕ) (hj : j ≤ D) (a : S.Field j) :
    Q.packet D (YM.OPE.sole 0) (YM.OPE.sole a : Labels S (fun _ : Unit => j)) 0 =
      F.sector.derivatives.rise hj a :=
  YMReview.OPE.single_field F Q D j hj a
end FieldDictionary

/-!
## 6. Existence with the public properties on the same hierarchy

The family is chosen before the requested volume sequence p. For each
strictly increasing p, the theorem selects a subsequence q and one hierarchy
T satisfying both the public properties and the explicit OPE target. It does
not prove uniqueness across those choices.

This is the separate OPE endpoint, not an identification of its existential
witness with the one chosen by `combined_acceptance`. The adapter in section
1 can also be applied directly to any particular hierarchy whose source OPE
has been obtained; no second choice is needed for that application.
-/

theorem constructed_with_public_properties (g : GaugeGroup) (hg : g.IsSimple) :
    ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ OPE.CommonOPE T :=
  OPE.constructed g hg

/-!
The tests above establish controlled finite-truncation asymptotics and their
field dictionary. They do not establish convergence as D tends to infinity,
unique coefficients under every change of field normalization or OPE
prescription, or the numerical Yang–Mills perturbative coefficients. They
also do not identify phases merely because their coefficients agree.
-/

#print axioms explicit_radius_from_source
#print axioms coefficient_bound
#print axioms remainder_uniform_in_state
#print axioms difference_of_states
#print axioms channel_assembly
#print axioms single_insertion_recovered
#print axioms constructed_with_public_properties
end YMReview.Examples.CommonOPE
