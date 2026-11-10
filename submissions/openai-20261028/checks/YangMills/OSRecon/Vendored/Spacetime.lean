/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Vendored from OSreconstruction: spacetime, splitting maps, time reflection

Upstream: https://github.com/xiyin137/OSreconstruction — transcribed from the local
fork `cherkis/OSreconstruction` at commit `936defd39f199b38301c05e8caeae6b16eb7d167`
(upstream `main` at `135ed13` is identical on these ranges except for the
`push Not` tactic spelling, see below).

Source blocks:
* `OSReconstruction/Wightman/OperatorDistribution.lean` 56-59
  (`SpacetimeDim`, `SchwartzSpacetime`);
* `OSReconstruction/Wightman/Reconstruction/Core.lean` 68-71
  (`NPointDomain`, `SchwartzNPoint`), 2860-2865 (`timeReflection`, `timeReflectionN`),
  2867-2955 (measure preservation), 2958-2991 (involution, norm, smoothness),
  3106-3149 (`tsupport_precomp_subset`, continuity lemmas);
* `OSReconstruction/Wightman/SchwartzTensorProduct.lean` 222-318
  (`splitFirst`, `splitLast` and their norm lemmas).

Deviations from the upstream text, all recorded here:
1. `private` removed from `timeReflection_nnnorm_eq`, `timeReflectionN_norm_eq`,
   `contDiff_timeReflectionN`, `tsupport_precomp_subset`, `continuous_timeReflectionN`,
   `continuous_splitFirst`, `continuous_splitLast`, because other vendored files use them.
2. The `omit [NeZero d] in` prefixes are dropped where the section variable is not in scope.
3. Upstream's global `set_option backward.isDefEq.respectTransparency false` is not set.
4. Mathlib v4.33 `simpa` no longer closes definitional gaps: in
   `reverseNPoint_measurePreserving` a `change` to the underlying `Equiv.piCongrLeft` is
   inserted before the `simpa`, and in `continuous_timeReflectionN` the two type-ascribed
   `simpa … using (… : Continuous …)` terms are first bound with `have h : Continuous … := …`.
   Statements unchanged.
5. Rename: upstream's `timeReflection_measurePreserving` is `timeReflection_measurePreserving_pi`
   here, because OSforGFF declares a root-level lemma of that name
   (`OSforGFF/OS/OS3_MixedRepInfra.lean:111`) and both must live in one environment.

Reason for vendoring: OSreconstruction is on Lean `v4.29.0` and cannot be `require`d from
this `v4.33.0-rc1` project. Replace by `import OSReconstruction.…` once toolchains align.
-/

noncomputable section

open scoped SchwartzMap
open Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The spacetime dimension type for Schwartz functions.
    For d spatial dimensions, spacetime is ℝ^{d+1}. -/
abbrev SpacetimeDim (d : ℕ) := Fin (d + 1) → ℝ

/-- Schwartz space on d+1 dimensional spacetime with complex values -/
abbrev SchwartzSpacetime (d : ℕ) := SchwartzMap (SpacetimeDim d) ℂ

/-- The space of n copies of spacetime for n-point functions -/
abbrev NPointDomain (d n : ℕ) := Fin n → SpacetimeDim d

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPoint (d n : ℕ) := SchwartzMap (NPointDomain d n) ℂ

/-! ### Splitting maps (from `SchwartzTensorProduct.lean`) -/

section Split

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The splitting map: given x : Fin (m+k) → E, extract the first m components.
    This sends x to (x₁, ..., xₘ). -/
def splitFirst (m k : ℕ) (x : Fin (m + k) → E) : Fin m → E :=
  fun i => x (Fin.castAdd k i)

/-- The splitting map: given x : Fin (m+k) → E, extract the last k components.
    This sends x to (x_{m+1}, ..., x_{m+k}). -/
def splitLast (m k : ℕ) (x : Fin (m + k) → E) : Fin k → E :=
  fun j => x (Fin.natAdd m j)

@[simp]
theorem splitFirst_fin_append {m k : ℕ} (x : Fin m → E) (y : Fin k → E) :
    splitFirst m k (Fin.append x y) = x := by
  funext i
  simp [splitFirst, Fin.append_left]

@[simp]
theorem splitLast_fin_append {m k : ℕ} (x : Fin m → E) (y : Fin k → E) :
    splitLast m k (Fin.append x y) = y := by
  funext j
  simp [splitLast, Fin.append_right]

/-- splitFirst is a continuous linear map (projection). -/
theorem splitFirst_continuousLinear (m k : ℕ) :
    Continuous (splitFirst m k : (Fin (m + k) → E) → (Fin m → E)) :=
  continuous_pi fun i => continuous_apply _

/-- splitLast is a continuous linear map (projection). -/
theorem splitLast_continuousLinear (m k : ℕ) :
    Continuous (splitLast m k : (Fin (m + k) → E) → (Fin k → E)) :=
  continuous_pi fun j => continuous_apply _

/-- splitFirst as a ContinuousLinearMap (projection to first m components). -/
noncomputable def splitFirstCLM (m k : ℕ) :
    (Fin (m + k) → E) →L[ℝ] (Fin m → E) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E) (Fin.castAdd k i)

/-- splitLast as a ContinuousLinearMap (projection to last k components). -/
noncomputable def splitLastCLM (m k : ℕ) :
    (Fin (m + k) → E) →L[ℝ] (Fin k → E) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + k)) (φ := fun _ => E) (Fin.natAdd m j)

@[simp]
theorem splitFirstCLM_apply (m k : ℕ) (x : Fin (m + k) → E) :
    splitFirstCLM m k x = splitFirst m k x := rfl

@[simp]
theorem splitLastCLM_apply (m k : ℕ) (x : Fin (m + k) → E) :
    splitLastCLM m k x = splitLast m k x := rfl

/-- The norm of splitFirst x is at most the norm of x. -/
theorem splitFirst_norm_le (m k : ℕ) (x : Fin (m + k) → E) :
    ‖splitFirst m k x‖ ≤ ‖x‖ := by
  simp only [splitFirst, Pi.norm_def]
  exact_mod_cast Finset.sup_le fun b _ =>
    Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ (Fin.castAdd k b))

/-- The norm of splitLast x is at most the norm of x. -/
theorem splitLast_norm_le (m k : ℕ) (x : Fin (m + k) → E) :
    ‖splitLast m k x‖ ≤ ‖x‖ := by
  simp only [splitLast, Pi.norm_def]
  exact_mod_cast Finset.sup_le fun b _ =>
    Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ (Fin.natAdd m b))

/-- The operator norm of splitFirstCLM is at most 1. -/
theorem splitFirstCLM_opNorm_le (m k : ℕ) :
    ‖splitFirstCLM m k (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [splitFirstCLM_apply, one_mul]; exact splitFirst_norm_le m k x

/-- The operator norm of splitLastCLM is at most 1. -/
theorem splitLastCLM_opNorm_le (m k : ℕ) :
    ‖splitLastCLM m k (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [splitLastCLM_apply, one_mul]; exact splitLast_norm_le m k x

/-- The norm of x is at most ‖splitFirst x‖ + ‖splitLast x‖.
    This follows from ‖x‖ = max(‖splitFirst x‖, ‖splitLast x‖) ≤ sum. -/
theorem norm_le_splitFirst_add_splitLast (m k : ℕ) (x : Fin (m + k) → E) :
    ‖x‖ ≤ ‖splitFirst m k x‖ + ‖splitLast m k x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  by_cases hj : j.val < m
  · -- j is in first m components: ‖x j‖ ≤ ‖splitFirst x‖ ≤ sum
    have heq : x j = splitFirst m k x ⟨j.val, hj⟩ := rfl
    rw [heq]
    exact (norm_le_pi_norm _ _).trans (le_add_of_nonneg_right (norm_nonneg _))
  · -- j is in last k components: ‖x j‖ ≤ ‖splitLast x‖ ≤ sum
    push Not at hj
    have hjk : j.val - m < k := by omega
    have heq : x j = splitLast m k x ⟨j.val - m, hjk⟩ := by
      show x j = x (Fin.natAdd m ⟨j.val - m, hjk⟩)
      congr 1; exact Fin.ext (by simp [Fin.natAdd]; omega)
    rw [heq]
    exact (norm_le_pi_norm _ _).trans (le_add_of_nonneg_left (norm_nonneg _))

end Split

/-! ### Time reflection (from `Core.lean`) -/

variable (d : ℕ) [NeZero d]

/-- Time reflection operator on Euclidean points: θ(τ, x⃗) = (-τ, x⃗) -/
def timeReflection (x : SpacetimeDim d) : SpacetimeDim d :=
  fun i => if i = 0 then -x 0 else x i

/-- Time reflection on n-point configurations -/
def timeReflectionN {n : ℕ} (x : NPointDomain d n) : NPointDomain d n :=
  fun i => timeReflection d (x i)

/-- Euclidean spacetime translation preserves Lebesgue measure. -/
theorem translate_spacetime_measurePreserving (a : SpacetimeDim d) :
    MeasureTheory.MeasurePreserving
      (fun x : SpacetimeDim d => x + a) MeasureTheory.volume MeasureTheory.volume := by
  simpa [Pi.add_apply] using
    (MeasureTheory.measurePreserving_add_right
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)) a)

/-- Componentwise Euclidean spacetime translation preserves Lebesgue measure on
`n`-point configuration space. -/
theorem translateNPoint_measurePreserving {n : ℕ} (a : SpacetimeDim d) :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i : Fin n => x i + a)
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show (fun x : NPointDomain d n => fun i : Fin n => x i + a) =
      (fun x : NPointDomain d n => fun i : Fin n => (fun y : SpacetimeDim d => y + a) (x i)) by
      rfl]
  exact MeasureTheory.volume_preserving_pi
    (fun _ : Fin n => translate_spacetime_measurePreserving (d := d) a)

/-- Time reflection preserves Lebesgue measure on spacetime. -/
theorem timeReflection_measurePreserving_pi :
    MeasureTheory.MeasurePreserving (timeReflection d) MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show timeReflection (d := d) =
      (fun (x : SpacetimeDim d) (i : Fin (d + 1)) =>
        (if i = 0 then Neg.neg else id) (x i)) by
      funext x i
      by_cases hi : i = 0
      · subst hi
        simp [timeReflection]
      · simp [timeReflection, hi]]
  exact MeasureTheory.volume_preserving_pi (fun i : Fin (d + 1) => by
    by_cases hi : i = 0
    · simpa [hi] using
        (MeasureTheory.Measure.measurePreserving_neg
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    · simpa [hi] using
        (MeasureTheory.MeasurePreserving.id (MeasureTheory.volume : MeasureTheory.Measure ℝ)))

/-- Time reflection preserves Lebesgue measure on n-point configuration space. -/
theorem timeReflectionN_measurePreserving {n : ℕ} :
    MeasureTheory.MeasurePreserving
      (timeReflectionN (d := d) (n := n)) MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show timeReflectionN (d := d) (n := n) =
      (fun (x : NPointDomain d n) (i : Fin n) => timeReflection (d := d) (x i)) by
      funext x i
      rfl]
  exact MeasureTheory.volume_preserving_pi
    (fun _ : Fin n => timeReflection_measurePreserving_pi (d := d))

/-- Reversing the order of points preserves Lebesgue measure on n-point configuration space. -/
theorem reverseNPoint_measurePreserving {n : ℕ} :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i : Fin n => x (Fin.rev i))
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  have heq : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => SpacetimeDim d) e : _ → _)
      = (fun x : NPointDomain d n => fun i : Fin n => x (Fin.rev i)) := by
    funext x
    let x' : (a : Fin n) → (fun _ : Fin n => SpacetimeDim d) (e a) := x
    funext i
    change (Equiv.piCongrLeft (fun _ : Fin n => SpacetimeDim d) e) x' i = x (Fin.rev i)
    simpa [e] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => SpacetimeDim d) (e := e) x'
        (Fin.rev i))
  exact heq ▸
    (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin n => SpacetimeDim d) e)

/-- The real OS reflection map (reverse the point order and reflect Euclidean time) preserves
    Lebesgue measure on configuration space. -/
theorem osReflectionN_measurePreserving {n : ℕ} :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i : Fin n => timeReflection d (x (Fin.rev i)))
      MeasureTheory.volume MeasureTheory.volume := by
  let revMap : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  let thetaMap : NPointDomain d n → NPointDomain d n := timeReflectionN (d := d) (n := n)
  have hcomp :
      (fun x : NPointDomain d n => fun i : Fin n => timeReflection d (x (Fin.rev i))) =
        thetaMap ∘ revMap := by
    rfl
  rw [hcomp]
  exact (timeReflectionN_measurePreserving (d := d) (n := n)).comp
    (reverseNPoint_measurePreserving (d := d) (n := n))

/-- Time reflection is an involution: θ(θx) = x. -/
theorem timeReflection_timeReflection (x : SpacetimeDim d) :
    timeReflection d (timeReflection d x) = x := by
  funext j; simp only [timeReflection]; by_cases hj : j = 0 <;> simp [hj]

/-- Time reflection preserves the NNNorm of spacetime vectors. -/
theorem timeReflection_nnnorm_eq (y : SpacetimeDim d) :
    ‖timeReflection d y‖₊ = ‖y‖₊ := by
  simp only [Pi.nnnorm_def, timeReflection]
  apply Finset.sup_congr rfl; intro j _
  by_cases hj : j = 0
  · subst hj; simp [nnnorm_neg]
  · simp [if_neg hj]

/-- Time reflection preserves the norm of n-point configurations. -/
theorem timeReflectionN_norm_eq {n : ℕ} (x : NPointDomain d n) :
    ‖timeReflectionN d x‖ = ‖x‖ := by
  simp only [Pi.norm_def, timeReflectionN]
  congr 1
  apply Finset.sup_congr rfl; intro i _
  exact_mod_cast timeReflection_nnnorm_eq d (x i)

/-- Time reflection on n-point domains is smooth (it is linear). -/
theorem contDiff_timeReflectionN {n : ℕ} {m : WithTop ℕ∞} :
    ContDiff ℝ m (timeReflectionN (n := n) d) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  show ContDiff ℝ m fun x => timeReflectionN d x i j
  simp only [timeReflectionN, timeReflection]
  by_cases hj : j = 0
  · subst hj; simp only [ite_true]
    exact (contDiff_apply_apply ℝ ℝ i (0 : Fin (d + 1))).neg
  · simp only [if_neg hj]
    exact contDiff_apply_apply ℝ ℝ i j

theorem tsupport_precomp_subset {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

theorem continuous_timeReflectionN {n : ℕ} :
    Continuous (timeReflectionN d (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have h : Continuous fun x : NPointDomain d n => -x i 0 :=
      (((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg
    simpa [timeReflectionN, timeReflection] using h
  · have h : Continuous fun x : NPointDomain d n => x i μ :=
      (continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
        (continuous_apply i : Continuous fun x : NPointDomain d n => x i)
    simpa [timeReflectionN, timeReflection, hμ] using h

theorem continuous_splitFirst {n m : ℕ} :
    Continuous (splitFirst n m : NPointDomain d (n + m) → NPointDomain d n) := by
  apply continuous_pi
  intro i
  simpa [splitFirst] using
    (continuous_apply (Fin.castAdd m i) :
      Continuous fun x : NPointDomain d (n + m) => x (Fin.castAdd m i))

theorem continuous_splitLast {n m : ℕ} :
    Continuous (splitLast n m : NPointDomain d (n + m) → NPointDomain d m) := by
  apply continuous_pi
  intro i
  simpa [splitLast] using
    (continuous_apply (Fin.natAdd n i) :
      Continuous fun x : NPointDomain d (n + m) => x (Fin.natAdd n i))

end
