/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import YangMills.OSRecon.Vendored.TensorProduct
import YangMills.OSRecon.Vendored.ZeroDiagonal

/-!
# Vendored from OSreconstruction: Borchers sequences and OS conjugation

Upstream: https://github.com/xiyin137/OSreconstruction, local fork
`cherkis/OSreconstruction` at commit `936defd39f199b38301c05e8caeae6b16eb7d167`.

Source: `OSReconstruction/Wightman/Reconstruction/Core.lean` 164-170
(`BorchersSequence`), 3004-3104 (`SchwartzNPoint.timeReflect`, `osConj`,
`osConjTensorProduct` and their lemmas), 3245-3383 (the admissibility lemma
`VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion`).

Deviations (statements unchanged): in the admissibility lemma the step
`simpa [osConjTensorProduct, tensorProduct_apply] using hx` is replaced by `exact hx`
(Mathlib v4.33 `simpa` does not close the definitional unfolding of the coercion).
The algebraic instances on `BorchersSequence` (`Core.lean` 175-215) are not needed to
state the axioms and are not transcribed.
-/

noncomputable section

open scoped SchwartzMap
open Topology

set_option linter.unusedSectionVars false

/-- A Borchers sequence: a finite sequence of test functions, one for each n.

    The `funcs` field is indexed by all n ∈ ℕ, with `bound_spec` ensuring all
    components beyond `bound` are zero. This simplifies algebraic operations
    (addition, scalar multiplication, etc.) compared to a dependent-type formulation. -/
structure BorchersSequence (d : ℕ) where
  /-- For each n, a test function on n copies of spacetime -/
  funcs : (n : ℕ) → SchwartzNPoint d n
  /-- A bound on the support: all components beyond this are zero -/
  bound : ℕ
  /-- All components beyond the bound are zero -/
  bound_spec : ∀ n, bound < n → funcs n = 0

variable {d : ℕ} [NeZero d]

/-- Time reflection on n-point Schwartz functions.
    (θf)(x₁,...,xₙ) = f(θx₁,...,θxₙ) where θ(τ,x⃗) = (-τ,x⃗).

    This is the correct involution for the Osterwalder-Schrader inner product.
    The OS reflection positivity uses ⟨F, G⟩_OS = Σ S_{n+m}((θf̄)_n ⊗ g_m),
    NOT the Borchers involution (which includes argument reversal).

    Reference: Osterwalder-Schrader, Commun. Math. Phys. 31 (1973), Axiom E2 -/
def SchwartzNPoint.timeReflect {n : ℕ} (f : SchwartzNPoint d n) : SchwartzNPoint d n where
  toFun := fun x => f (timeReflectionN d x)
  smooth' := by exact f.smooth'.comp (contDiff_timeReflectionN d)
  decay' := by
    intro k l
    obtain ⟨C, hC⟩ := f.decay' k l
    refine ⟨C, fun x => ?_⟩
    let θLE : NPointDomain d n ≃ₗ[ℝ] NPointDomain d n :=
      { toFun := timeReflectionN d
        invFun := timeReflectionN d
        left_inv := fun x => funext fun i => timeReflection_timeReflection d (x i)
        right_inv := fun x => funext fun i => timeReflection_timeReflection d (x i)
        map_add' := fun x y => by
          funext i j; simp only [timeReflectionN, timeReflection, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c x => by
          funext i j
          simp only [timeReflectionN, timeReflection, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]
          split_ifs <;> ring }
    let θLIE : NPointDomain d n ≃ₗᵢ[ℝ] NPointDomain d n :=
      { θLE with
        norm_map' := fun x => timeReflectionN_norm_eq d x }
    have hcomp : (fun x => f (timeReflectionN d x)) = f ∘ θLIE := rfl
    rw [hcomp, θLIE.norm_iteratedFDeriv_comp_right (𝕜 := ℝ) f x l,
      show ‖x‖ = ‖θLIE x‖ from (θLIE.norm_map x).symm]
    exact hC _

@[simp]
theorem SchwartzNPoint.timeReflect_apply {n : ℕ} (f : SchwartzNPoint d n)
    (x : NPointDomain d n) :
    f.timeReflect x = f (timeReflectionN d x) := rfl

/-- Time reflection is an involution on Schwartz functions. -/
theorem SchwartzNPoint.timeReflect_timeReflect {n : ℕ} (f : SchwartzNPoint d n) :
    f.timeReflect.timeReflect = f := by
  ext x; simp only [SchwartzNPoint.timeReflect_apply]
  congr 1; funext i; exact timeReflection_timeReflection d (x i)

/-- Time reflection does not increase Schwartz seminorms. -/
theorem SchwartzNPoint.seminorm_timeReflect_le {n : ℕ} (k l : ℕ)
    (f : SchwartzNPoint d n) :
    SchwartzMap.seminorm ℝ k l f.timeReflect ≤ SchwartzMap.seminorm ℝ k l f := by
  refine SchwartzMap.seminorm_le_bound ℝ k l f.timeReflect
    (by positivity) ?_
  intro x
  let θLE : NPointDomain d n ≃ₗ[ℝ] NPointDomain d n :=
    { toFun := timeReflectionN d
      invFun := timeReflectionN d
      left_inv := fun y => funext fun i => timeReflection_timeReflection d (y i)
      right_inv := fun y => funext fun i => timeReflection_timeReflection d (y i)
      map_add' := fun y z => by
        funext i μ
        simp only [timeReflectionN, timeReflection, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c y => by
        funext i μ
        simp only [timeReflectionN, timeReflection, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        split_ifs <;> ring }
  let θLIE : NPointDomain d n ≃ₗᵢ[ℝ] NPointDomain d n :=
    { θLE with
      norm_map' := fun y => timeReflectionN_norm_eq d y }
  have hcomp : (fun y => f (timeReflectionN d y)) = f ∘ θLIE := rfl
  rw [show ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f.timeReflect) x‖ =
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => f (timeReflectionN d y)) x‖ by rfl]
  rw [hcomp, θLIE.norm_iteratedFDeriv_comp_right (𝕜 := ℝ) f x l,
    show ‖x‖ = ‖θLIE x‖ from (θLIE.norm_map x).symm]
  exact SchwartzMap.le_seminorm ℝ k l f (θLIE x)

/-- The Osterwalder-Schrader conjugation: time reflection + complex conjugation.
    (θf̄)(x₁,...,xₙ) = conj(f(θx₁,...,θxₙ))

    This is the correct involution for the OS inner product. Compare with
    `borchersConj` (argument reversal + conjugation) for Wightman functions.

    Reference: Osterwalder-Schrader, Commun. Math. Phys. 31 (1973), §2 -/
def SchwartzNPoint.osConj {n : ℕ} (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  f.timeReflect.conj

@[simp]
theorem SchwartzNPoint.osConj_apply {n : ℕ} (f : SchwartzNPoint d n)
    (x : NPointDomain d n) :
    f.osConj x = starRingEnd ℂ (f (timeReflectionN d x)) := rfl

/-- The OS conjugation does not increase Schwartz seminorms. -/
theorem SchwartzNPoint.seminorm_osConj_le {n : ℕ} (k l : ℕ)
    (f : SchwartzNPoint d n) :
    SchwartzMap.seminorm ℝ k l f.osConj ≤ SchwartzMap.seminorm ℝ k l f := by
  exact (SchwartzMap.seminorm_conj_le k l f.timeReflect).trans
    (SchwartzNPoint.seminorm_timeReflect_le (d := d) k l f)

/-- The OS conjugated tensor product: (θf̄) ⊗ g.
    This is the pairing used in the OS inner product for Schwinger functions:
    ⟨F, G⟩_OS = Σ S_{n+m}((θf̄)_n ⊗ g_m)

    Compare with `conjTensorProduct` (Borchers involution) used in
    `WightmanInnerProduct`. -/
def SchwartzNPoint.osConjTensorProduct {m k : ℕ} (f : SchwartzNPoint d m)
    (g : SchwartzNPoint d k) : SchwartzNPoint d (m + k) :=
  f.osConj.tensorProduct g

/-- If both factors are supported in the ordered positive-time region then the
    OS-conjugated tensor product `(θf̄) ⊗ g` is
    automatically zero-diagonal.

    Geometrically, `f.osConj` is supported where all first-block times are
    strictly negative and decreasing, while `g` stays on the ordered positive-time
    region. Hence every configuration in the topological support of
    `(θf̄) ⊗ g` has all time coordinates distinct, so the coincidence locus is
    avoided before taking any derivatives. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hg : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    VanishesToInfiniteOrderOnCoincidence (f.osConjTensorProduct g) := by
  let A : Set (NPointDomain d (n + m)) :=
    { x | splitFirst n m x ∈ OrderedNegativeTimeRegion d n }
  let B : Set (NPointDomain d (n + m)) :=
    { x | splitLast n m x ∈ OrderedPositiveTimeRegion d m }
  have hosConj :
      tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n := by
    intro x hx i
    have hxpre :
        timeReflectionN d x ∈ tsupport (f : NPointDomain d n → ℂ) := by
      exact tsupport_precomp_subset (f := (f : NPointDomain d n → ℂ))
        (h := timeReflectionN d) (continuous_timeReflectionN (d := d))
        ((tsupport_comp_subset (g := starRingEnd ℂ) (map_zero _) (fun y : NPointDomain d n =>
          f (timeReflectionN d y))) hx)
    have hpos := hf hxpre
    constructor
    · have : 0 < timeReflectionN d x i 0 := (hpos i).1
      simpa [timeReflectionN, timeReflection] using this
    · intro j hij
      have : timeReflectionN d x i 0 < timeReflectionN d x j 0 := (hpos i).2 j hij
      simpa [timeReflectionN, timeReflection] using this
  have hA :
      tsupport (fun x : NPointDomain d (n + m) => f.osConj (splitFirst n m x)) ⊆ A := by
    intro x hx
    exact hosConj <|
      tsupport_precomp_subset (f := ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        (h := splitFirst n m) (continuous_splitFirst (d := d)) hx
  have hB :
      tsupport (fun x : NPointDomain d (n + m) => g (splitLast n m x)) ⊆ B := by
    intro x hx
    exact hg <|
      tsupport_precomp_subset (f := (g : NPointDomain d m → ℂ))
        (h := splitLast n m) (continuous_splitLast (d := d)) hx
  have hsupport :
      tsupport (((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ)) ⊆ A ∩ B := by
    intro x hx
    have hxprod :
        x ∈ tsupport (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y) * g (splitLast n m y)) := by
      exact hx
    refine ⟨hA ((tsupport_mul_subset_left (f := fun y : NPointDomain d (n + m) =>
      f.osConj (splitFirst n m y)) (g := fun y : NPointDomain d (n + m) =>
      g (splitLast n m y))) hxprod), ?_⟩
    exact hB ((tsupport_mul_subset_right (f := fun y : NPointDomain d (n + m) =>
      f.osConj (splitFirst n m y)) (g := fun y : NPointDomain d (n + m) =>
      g (splitLast n m y))) hxprod)
  have hdisj : Disjoint (A ∩ B) (CoincidenceLocus d (n + m)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxAB hxcoin
    rcases hxAB with ⟨hxA, hxB⟩
    rcases hxcoin with ⟨i, j, hij, hijEq⟩
    by_cases hi : i.1 < n
    · by_cases hj : j.1 < n
      · let i' : Fin n := ⟨i.1, hi⟩
        let j' : Fin n := ⟨j.1, hj⟩
        have hi_cast : Fin.castAdd m i' = i := by
          ext
          simp [i']
        have hj_cast : Fin.castAdd m j' = j := by
          ext
          simp [j']
        have hEq0 : splitFirst n m x i' 0 = splitFirst n m x j' 0 := by
          simpa [splitFirst, hi_cast, hj_cast] using congrArg (fun y : SpacetimeDim d => y 0) hijEq
        have hij' : i' ≠ j' := by
          intro hij'
          apply hij
          simpa [hi_cast, hj_cast] using congrArg (fun t : Fin n => Fin.castAdd m t) hij'
        rcases lt_or_gt_of_ne hij' with hij'_lt | hij'_gt
        · have hlt : splitFirst n m x j' 0 < splitFirst n m x i' 0 := (hxA i').2 j' hij'_lt
          exact (lt_irrefl (splitFirst n m x j' 0)) (hEq0 ▸ hlt)
        · have hlt : splitFirst n m x i' 0 < splitFirst n m x j' 0 := (hxA j').2 i' hij'_gt
          exact (lt_irrefl (splitFirst n m x i' 0)) (hEq0.symm ▸ hlt)
      · let i' : Fin n := ⟨i.1, hi⟩
        let j' : Fin m := ⟨j.1 - n, by omega⟩
        have hi_cast : Fin.castAdd m i' = i := by
          ext
          simp [i']
        have hj_cast : Fin.natAdd n j' = j := by
          ext
          simp [j']
          omega
        have hneg : splitFirst n m x i' 0 < 0 := (hxA i').1
        have hpos : 0 < splitLast n m x j' 0 := (hxB j').1
        have hEq0 : splitFirst n m x i' 0 = splitLast n m x j' 0 := by
          simpa [splitFirst, splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        linarith
    · by_cases hj : j.1 < n
      · let i' : Fin m := ⟨i.1 - n, by omega⟩
        let j' : Fin n := ⟨j.1, hj⟩
        have hi_cast : Fin.natAdd n i' = i := by
          ext
          simp [i']
          omega
        have hj_cast : Fin.castAdd m j' = j := by
          ext
          simp [j']
        have hpos : 0 < splitLast n m x i' 0 := (hxB i').1
        have hneg : splitFirst n m x j' 0 < 0 := (hxA j').1
        have hEq0 : splitLast n m x i' 0 = splitFirst n m x j' 0 := by
          simpa [splitFirst, splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        linarith
      · let i' : Fin m := ⟨i.1 - n, by omega⟩
        let j' : Fin m := ⟨j.1 - n, by omega⟩
        have hi_cast : Fin.natAdd n i' = i := by
          ext
          simp [i']
          omega
        have hj_cast : Fin.natAdd n j' = j := by
          ext
          simp [j']
          omega
        have hEq0 : splitLast n m x i' 0 = splitLast n m x j' 0 := by
          simpa [splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        have hij' : i' ≠ j' := by
          intro hij'
          apply hij
          simpa [hi_cast, hj_cast] using congrArg (fun t : Fin m => Fin.natAdd n t) hij'
        rcases lt_or_gt_of_ne hij' with hij'_lt | hij'_gt
        · have hlt : splitLast n m x i' 0 < splitLast n m x j' 0 := (hxB i').2 j' hij'_lt
          exact (lt_irrefl (splitLast n m x i' 0)) (hEq0 ▸ hlt)
        · have hlt : splitLast n m x j' 0 < splitLast n m x i' 0 := (hxB j').2 i' hij'_gt
          exact (lt_irrefl (splitLast n m x j' 0)) (hEq0.symm ▸ hlt)
  exact VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
    (f := f.osConjTensorProduct g) (hdisj.mono_left hsupport)

end
