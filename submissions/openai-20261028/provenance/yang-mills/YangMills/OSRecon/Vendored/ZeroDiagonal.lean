/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import YangMills.OSRecon.Vendored.Spacetime

/-!
# Vendored from OSreconstruction: the zero-diagonal test space `°S`

Upstream: https://github.com/xiyin137/OSreconstruction, local fork
`cherkis/OSreconstruction` at commit `936defd39f199b38301c05e8caeae6b16eb7d167`.

Source: `OSReconstruction/Wightman/Reconstruction/Core.lean` 1553-1650 (regions,
coincidence locus, `VanishesToInfiniteOrderOnCoincidence`), 2570-2660
(`zeroDiagonalSubmodule`, `ZeroDiagonalSchwartz`, `ofClassical`), 2664-2669
(`VanishesToInfiniteOrderOnCoincidence.zero`), 2739-2745 (`ofClassical_zero`),
2825-2858 (`SchwingerFunctions`, ordered support ⟹ zero-diagonal).

Deviations (statements unchanged, proofs adapted to Mathlib v4.33):
1. `zeroDiagonalSubmodule.add_mem'`/`smul_mem'`: `simpa using` replaced by `change … ; exact`
   (v4.33 `simpa` no longer closes the definitional gap `⇑(f + g) = ⇑f + ⇑g`).
2. `instContinuousAddZeroDiagonalSchwartz`, `instContinuousConstSMulZeroDiagonalSchwartz`:
   `by delta …; infer_instance` replaced by `inferInstanceAs`.
3. `ofClassical_of_vanishes`/`_of_not_vanishes`: `simp [ofClassical, h]` replaced by
   `exact dif_pos h` / `exact dif_neg h`.
4. Two `simpa` → `simp` (linter).
Upstream sets `set_option backward.isDefEq.respectTransparency false` for the whole file;
it is not needed here.
-/

noncomputable section

open scoped SchwartzMap
open Topology

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

/-- The positive Euclidean time region: n-point configurations with all τᵢ > 0. -/
def PositiveTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, x i 0 > 0 }

/-- The OS-I ordered positive-time region: `0 < x₁⁰ < ... < xₙ⁰`.

    This is the support surface used in the positivity axiom `E2`, matching the
    test-function space `S^<_{+}` in OS I. -/
def OrderedPositiveTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, 0 < x i 0 ∧ ∀ j : Fin n, i < j → x i 0 < x j 0 }

/-- The time-reflected ordered region: all times are negative and strictly decrease. -/
def OrderedNegativeTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, x i 0 < 0 ∧ ∀ j : Fin n, i < j → x j 0 < x i 0 }

theorem OrderedPositiveTimeRegion_subset_positiveTimeRegion (d n : ℕ) :
    OrderedPositiveTimeRegion d n ⊆ PositiveTimeRegion d n := by
  intro x hx i
  exact (hx i).1

/-- The coincidence locus where at least two Euclidean arguments coincide. -/
def CoincidenceLocus (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∃ i j : Fin n, i ≠ j ∧ x i = x j }

/-- The one-point coincidence locus is empty. -/
theorem coincidenceLocus_one_eq_empty {d : ℕ} :
    CoincidenceLocus d 1 = ∅ := by
  ext x
  simp [CoincidenceLocus]

theorem not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion
    {d n : ℕ} {x : NPointDomain d n}
    (hx : x ∈ OrderedPositiveTimeRegion d n) :
    x ∉ CoincidenceLocus d n := by
  intro hcoin
  rcases hcoin with ⟨i, j, hij, hijEq⟩
  rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
  · have htime : x i 0 < x j 0 := (hx i).2 j hij_lt
    have hEq0 : x i 0 = x j 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq
    exact (lt_irrefl (x i 0)) (hEq0 ▸ htime)
  · have htime : x j 0 < x i 0 := (hx j).2 i hij_gt
    have hEq0 : x j 0 = x i 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq.symm
    exact (lt_irrefl (x j 0)) (hEq0 ▸ htime)

theorem not_mem_CoincidenceLocus_of_mem_OrderedNegativeTimeRegion
    {d n : ℕ} {x : NPointDomain d n}
    (hx : x ∈ OrderedNegativeTimeRegion d n) :
    x ∉ CoincidenceLocus d n := by
  intro hcoin
  rcases hcoin with ⟨i, j, hij, hijEq⟩
  rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
  · have htime : x j 0 < x i 0 := (hx i).2 j hij_lt
    have hEq0 : x i 0 = x j 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq
    exact (lt_irrefl (x j 0)) (hEq0 ▸ htime)
  · have htime : x i 0 < x j 0 := (hx j).2 i hij_gt
    have hEq0 : x j 0 = x i 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq.symm
    exact (lt_irrefl (x i 0)) (hEq0 ▸ htime)

/-- A Schwartz test function vanishes to infinite order on the coincidence locus
    if every iterated Fréchet derivative vanishes at every coincident configuration.

    This is the current formal stand-in for the OS-I test space `°S`: in finite
    dimensions, vanishing of all iterated Fréchet derivatives is the coordinate-free
    formulation of “vanishes with all partial derivatives on every diagonal.” -/
def VanishesToInfiniteOrderOnCoincidence {d n : ℕ} (f : SchwartzNPoint d n) : Prop :=
  ∀ k : ℕ, ∀ x : NPointDomain d n, x ∈ CoincidenceLocus d n →
    iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ) x = 0

/-- Every one-point Schwartz test function is automatically zero-diagonal,
since there are no coincidence configurations. -/
theorem VanishesToInfiniteOrderOnCoincidence.one {d : ℕ}
    (f : SchwartzNPoint d 1) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro k x hx
  simp [coincidenceLocus_one_eq_empty (d := d)] at hx

theorem VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
    {d n : ℕ} (f : SchwartzNPoint d n)
    (hdisj : Disjoint (tsupport (f : NPointDomain d n → ℂ)) (CoincidenceLocus d n)) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro k x hxcoin
  have hx_not_tsupport : x ∉ tsupport (f : NPointDomain d n → ℂ) := by
    intro hxt
    exact Set.disjoint_left.mp hdisj hxt hxcoin
  have hx_not_support :
      x ∉ Function.support (iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ)) := by
    intro hx
    exact hx_not_tsupport
      ((support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) (f := ⇑f)) hx)
  by_contra hx_nonzero
  exact hx_not_support (by simp [Function.mem_support, hx_nonzero])

/-- The `ℂ`-submodule of Schwartz n-point functions vanishing to infinite order
    on the coincidence locus. -/
def zeroDiagonalSubmodule (d n : ℕ) : Submodule ℂ (SchwartzNPoint d n) where
  carrier := { f | VanishesToInfiniteOrderOnCoincidence f }
  zero_mem' := by
    intro k x hx
    by_cases hk : k = 0
    · subst hk
      ext m
      simp
    · change iteratedFDeriv ℝ k (fun _ : NPointDomain d n => (0 : ℂ)) x = 0
      exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) hk (0 : ℂ)) x
  add_mem' := by
    intro f g hf hg k x hx
    change iteratedFDeriv ℝ k ((f : NPointDomain d n → ℂ) + (g : NPointDomain d n → ℂ)) x = 0
    exact
      (iteratedFDeriv_add_apply
        ((f : SchwartzNPoint d n).smooth _).contDiffAt
        ((g : SchwartzNPoint d n).smooth _).contDiffAt).trans
        (by rw [hf k x hx, hg k x hx, zero_add])
  smul_mem' := by
    intro c f hf k x hx
    change iteratedFDeriv ℝ k (c • (f : NPointDomain d n → ℂ)) x = 0
    exact
      (iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := c)
        (((f : SchwartzNPoint d n).smooth _).contDiffAt)).trans
        (by rw [hf k x hx, smul_zero])

/-- The OS-I zero-diagonal Schwartz test space. -/
def ZeroDiagonalSchwartz (d n : ℕ) :=
  ↥(zeroDiagonalSubmodule d n)

instance instAddCommMonoidZeroDiagonalSchwartz (d n : ℕ) :
    AddCommMonoid (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instModuleZeroDiagonalSchwartz (d n : ℕ) :
    Module ℂ (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instTopologicalSpaceZeroDiagonalSchwartz (d n : ℕ) :
    TopologicalSpace (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instContinuousAddZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousAdd (ZeroDiagonalSchwartz d n) :=
  inferInstanceAs (ContinuousAdd (zeroDiagonalSubmodule d n))

instance instContinuousSMulZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousSMul ℂ (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instContinuousConstSMulZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousConstSMul ℂ (ZeroDiagonalSchwartz d n) :=
  inferInstanceAs (ContinuousConstSMul ℂ (zeroDiagonalSubmodule d n))

/-- A classical promotion from a Schwartz test function to the zero-diagonal
    subspace, with a junk zero fallback when the function is not in `°S`.

    This keeps definitions such as `OSInnerProduct` total while ensuring that,
    whenever a genuine zero-diagonal witness exists, the promoted term reduces
    to the intended branch. -/
noncomputable def ZeroDiagonalSchwartz.ofClassical {d n : ℕ}
    (f : SchwartzNPoint d n) : ZeroDiagonalSchwartz d n := by
  classical
  by_cases h : VanishesToInfiniteOrderOnCoincidence f
  · exact ⟨f, h⟩
  · exact 0

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_of_vanishes {d n : ℕ}
    (f : SchwartzNPoint d n) (h : VanishesToInfiniteOrderOnCoincidence f) :
    ZeroDiagonalSchwartz.ofClassical f = ⟨f, h⟩ := by
  classical
  exact dif_pos h

@[simp]
theorem ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes {d n : ℕ}
    (f : SchwartzNPoint d n) (h : VanishesToInfiniteOrderOnCoincidence f) :
    (ZeroDiagonalSchwartz.ofClassical f).1 = f := by
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f) h]

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_of_not_vanishes {d n : ℕ}
    (f : SchwartzNPoint d n) (h : ¬ VanishesToInfiniteOrderOnCoincidence f) :
    ZeroDiagonalSchwartz.ofClassical f = 0 := by
  classical
  exact dif_neg h

theorem VanishesToInfiniteOrderOnCoincidence.zero {d n : ℕ} :
    VanishesToInfiniteOrderOnCoincidence (0 : SchwartzNPoint d n) := by
  intro k x hx
  exact congrFun
    (iteratedFDeriv_fun_zero (𝕜 := ℝ) (n := k)
      (E := NPointDomain d n) (F := ℂ)) x

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_zero {d n : ℕ} :
    ZeroDiagonalSchwartz.ofClassical (0 : SchwartzNPoint d n) = 0 := by
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := (0 : SchwartzNPoint d n))
    (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n))]
  rfl

/-- Zero-diagonal Schwinger families, i.e. Euclidean correlation functionals
    defined only on the OS-I test space `°S`. This is the honest Wightman -> OS-I
    codomain before any separate extension to the full Schwartz space. -/
def ZeroDiagonalSchwingerFunctions (d : ℕ) := (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ

/-- Honest Schwinger functions (Euclidean correlators) on the corrected OS-I
    test space `°S = ZeroDiagonalSchwartz`.

    This is the notion that should be used for Schwinger data in the project. -/
abbrev SchwingerFunctions (d : ℕ) := ZeroDiagonalSchwingerFunctions d

/-- If a Schwartz test function is supported in the strict ordered positive-time
    region, then it vanishes to infinite order on the coincidence locus.

    This is the precise bridge from the OS-I positivity sector `S^<_{+}` to the
    zero-diagonal space `°S`: coincidence points lie outside the ordered-time
    region, and every iterated derivative is supported inside the support of the
    original Schwartz function. -/
theorem VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
    {d n : ℕ} (f : SchwartzNPoint d n)
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro k x hxcoin
  have hx_not_ord : x ∉ OrderedPositiveTimeRegion d n := by
    intro hxord
    exact (not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion hxord) hxcoin
  have hx_not_support :
      x ∉ Function.support (iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ)) := by
    intro hx
    have hx' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) (f := ⇑f) hx
    exact hx_not_ord (hsupp hx')
  by_contra hx_nonzero
  exact hx_not_support (by simp [Function.mem_support, hx_nonzero])

end
