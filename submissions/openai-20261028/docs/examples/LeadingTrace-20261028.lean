-- SPDX-License-Identifier: Apache-2.0
import CombinedAcceptance
import OctoberChain

/-!
# LeadingTrace: from the constructed field to its short-distance two-point law

This is a worked example for the OpenAI submission of 28 October 2026. Read it
alongside `OctoberChain.lean`, which explains the general construction interfaces.
The present file follows one observable through them: the centered trace of the
translation-normalized stress tensor in the selected phase.

The checked short-distance law is, in the construction's reference units,

  K₂(x) |x|^8 log²(1/|x|) → 3 dim(g) / π⁴ > 0,  as x → 0 with x ≠ 0.

Here K₂ is the *selected phase's* two-point function of the centered stress
trace. It is not an independently supplied scalar function. The lattice
convergence theorem first gives the mixed hierarchy; phase selection is a
further, algebraically specified step.

The proofs below are consequences and presentations of existing results. They
do not change the combined acceptance target, independently rederive the RG
estimates, or add a Comparator endpoint. Comments explain the intended physical
meaning; Lean checks the accompanying formal statements. See the adjacent
README for compilation and VS Code instructions.
-/

set_option autoImplicit false
noncomputable section
namespace YMReview.Examples.LeadingTrace
open YM YM.Table Filter Set MeasureTheory
open scoped Topology BigOperators

variable {g : YangMills.GaugeGroup} {C : Family g.core}
variable {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-!
## 1. Fix one construction witness before defining the observable

`C` specifies the Wilson family and its renormalized lattice insertions. `o`
contains the volume extraction sequence. `S` is the resulting unselected
continuum table. `F` retains the stress tensor, phase construction and
relativistic realization for these data.

The tensor is `F.sector.energy`; its components lie in `S.Field 4`.
`Trace.theta F 0` is its trace before centering. The construction selects
the table `F.α.ensemble F.α.atPoint`. The actual one-point expectation in this
table determines `Trace.meanExact F`; it is not a freely chosen subtraction.

Thus, writing τ = Σμ Tμμ and m = ⟨τ⟩ in that phase, the field below is
Θ = τ − m·1. The independent translation Ward check in `Accepted.translation`
uses this same stress tensor with its specified sign and coefficient.
The equalities here identify the field; they do not reprove the Ward identity.
-/

theorem selected_state_is_fixed :
    Trace.state F = F.α.ensemble F.α.atPoint := rfl

theorem centering_uses_the_phase_mean :
    Trace.traceField F = Trace.theta F 0 -
      (Trace.meanExact F : ℂ) • S.unit 4 :=
  Trace.traceField_eq F

theorem centered_one_point (x : Points 1) :
    S.useAt (Trace.state F) x
      (fun _ : Fin 1 => (⟨4, Trace.traceField F⟩ : S.Tag)) = 0 :=
  Trace.centered_zero F x

/-!
## 2. Define the two-point function using precisely this field and phase

`scalarKernel F n x` inserts `Trace.traceField F` at all n points. `K₂` is its
real part at the two positions `(x,0)`. At distinct points the kernel is real,
so this operation does not discard an uncontrolled imaginary component.

Since the field is centered, its two-point function is the connected trace
correlation: in physics notation ⟨Θ(x)Θ(0)⟩ = ⟨τ(x)τ(0)⟩ − m².
The displayed Lean statement uses the centered field directly.

The source trace analysis calls its centered field `TraceExtension.center F`.
`YMAFBridge.same_center` proves equality with the field used in the OS bridge.
This is an equality inside the same quotient field space, not a comparison
between two separately chosen theories.
-/

theorem two_point_is_selected_kernel (x : SpaceTime) :
    YMAFBridge.K₂ F x =
      (S.useAt (Trace.state F) (points ![x, 0])
        (fun _ : Fin 2 => (⟨4, Trace.traceField F⟩ : S.Tag))).re := rfl

theorem separated_kernel_is_real (x : Points 2) (hx : x ∈ conf 2) :
    star (YMOSBridge.scalarKernel F 2 x) = YMOSBridge.scalarKernel F 2 x :=
  YMOSBridge.scalarKernel_real F x hx

theorem source_and_OS_fields_agree :
    TraceExtension.center F = Trace.traceField F :=
  YMAFBridge.same_center F

/-!
## 3. Locate the field in the lattice-derived hierarchy

The quotient field Θ has a raw representative. At a finite cutoff, that
representative gives an actual insertion through `C.O`; OctoberChain spells
out the local section and its invertible finite-cutoff coefficient map.

The following specialization of the chain lemma supplies two raw labels,
fixed across N and p, whose classes are Θ. Their smeared lattice pair has a
full UV limit `row p` in every suitable fixed volume. Along `o.per`, those
pairings converge to the *mixed* correlation of Θ.

The test `t` is smooth, compactly supported and separated from coincidences.
`suitable p t` places its support inside the volume's comparison cell. The
statement makes neither a pointwise assertion at a coincidence nor a claim
that UV and IR limits can be interchanged.

Notice `S.useAt S` on the right. Θ is centered in the selected phase, but
evaluating that field in the mixed table does not make the two states equal.
In particular, this lemma alone does not identify the limit with `K₂`.
-/

theorem centered_trace_has_mixed_lattice_origin (hg : g.IsSimple)
    (h : Acceptance.Accepted hg F)
    (t : YangMills.WilsonFamily.SeparatedTest 2) :
    ∃ v : Fin 2 → C.book.Token,
      (∀ i, S.classTokens (v i) = (⟨4, Trace.traceField F⟩ : S.Tag)) ∧
      ∃ row : ℕ → ℂ,
        (∀ p, (YangMills.wilsonFamily C).suitable p t →
          Tendsto (fun N => (YangMills.wilsonFamily C).smear N p v t)
            atTop (𝓝 (row p))) ∧
        Tendsto (fun k => row (o.per k)) atTop
          (𝓝 (∫ x, t x * S.useAt S x
            (fun _ : Fin 2 => (⟨4, Trace.traceField F⟩ : S.Tag)))) :=
  Chain.every_field_word_has_lattice_origin hg h 2
    (fun _ => ⟨4, Trace.traceField F⟩) t

/-!
## 4. Pass from the mixed hierarchy to the selected phase

The mixed table determines its OS Hilbert space and ground-state algebra.
The certificate in `F` identifies phase expectations of whole words with
characters of the actual compressed insertion operators. It also represents
the mixed vacuum state by a probability measure on these characters.

The barycenter identity below is one consequence. The stronger connection
through products in that algebra is exposed by
`YMReview.Chain.phase_second_moments_are_ground_products`. A phase is not
specified merely by inventing an ensemble with the right average.

For `K₂`, the selected point is `F.α.atPoint`. No theorem here says that each
phase is itself a subsequential limit of the original periodic-volume states,
or that all phases have the same correlations.
-/

theorem mixed_expectations_are_phase_averages (hg : g.IsSimple)
    (h : Acceptance.Accepted hg F) (w : C.book.Word) (hw : Word.distinct w) :
    (∫ i, (F.α.ensemble i).expect w ∂F.α.space.μ) = S.expect w :=
  h.phase_os.phase_average w hw

/-!
## 5. Identify the source's time-axis correlator and its coefficient

`TraceExtension.euclidean F r` evaluates the same centered trace at opposed
time-axis points separated by r. Euclidean invariance and the scalar
transformation law identify the general separated two-point function with
this radial expression. The source lemma used by `K₂_radial` is
`YM.Trace.Verse.axis_shape`.

The source coefficient is initially written

  award G = 12 (d₂(G)² / b₀(G)²) dim(g) / π⁴.

The identity `Trace.Over.force_b` gives d₂ = −b₀/2. For a simple input group,
the denominator is nonzero; `canonical_award` simplifies this to
3 dim(g)/π⁴. This algebraic simplification is only the last step of the
substantive short-distance analysis.

Where does the analytic input come from? These declarations in the submission
provide a reading route; they are not replaced by the adapter below:

* `YM.Trace.wick_norm` computes the free curvature-square two-point coefficient
  by Wick contraction (`YM/TraceExtension/Foundation/Constant.lean`).
* `YM.Trace.Over.Scribe` records the rescaling comparison of the trace with
  that free field and the logarithmic clock (`.../Chart/Time.lean`).
* `YM.Trace.Verse.tagline` combines the field and clock limits with the free
  coefficient, using the selected-phase comparison (`.../Verse/Day.lean`).
* `YM.Trace.Verse.border` uses the spectral monotonicity to control perturbed
  separations. `outside` upgrades the controlled-subsequence analysis to a
  full positive-distance limit (`.../Verse/Cape.lean`).

The last step matters: subsequences used *inside a proof* need not weaken its
conclusion to subsequential convergence. Here `shortDistance` is a full limit.

### Literature normalization check: why the target is 3 dim(g)/π⁴

The references here support the numerical value used in this check. The
following calculation is an informal comparison with perturbation theory;
the Lean declarations below establish that the submitted construction has
that value, using its proved analytic estimates.

Use canonically normalized gauge fields, with the coupling in the commutator
term of their curvature, and write Q = Fᵃ_can,μν Fᵃ_can,μν, summing over both
orders of μ,ν. This convention must be distinguished from a curvature whose
action carries an overall 1/g². The free field-strength propagator in [OP,
eq. (5.15)] is

  ⟨Fᵃ_μν(x) Fᵇ_ρσ(0)⟩ = δᵃᵇ (I_μρ I_νσ − I_μσ I_νρ)/(π² |x|⁴),
  I_μν = δ_μν − 2 x_μ x_ν/|x|².

Two cross-contractions and the squared norm 2·4·3 = 24 of the antisymmetric
tensor give

  ⟨Q(x) Q(0)⟩_free,c = 48 dim(g)/(π⁴ |x|⁸).

The trace-anomaly identity [ZC, eq. (4.3)], translated to
β(g) = μ dg/dμ, is Tᵘ_ᵘ = β(g)[Q]/(2g). Their β(a_s) is a logarithmic
derivative with respect to μ², hence equals β(g)/g; it is not our β(g).
Writing β(g) = −b₀ g³ + O(g⁵) and ℓ = log(1/(Λ |x|)), one-loop running
g²(1/|x|) ∼ 1/(2 b₀ ℓ) gives β(g)/(2g) ∼ −1/(4ℓ). Consequently

  ⟨Θ(x) Θ(0)⟩_c ∼ (48/16) dim(g)/(π⁴ |x|⁸ ℓ²)
                   = 3 dim(g)/(π⁴ |x|⁸ ℓ²).

The phase's finite one-point subtraction does not change this leading
singularity, and a fixed Λ > 0 changes ℓ only by an additive constant.
For the position-space RG-improved calculation, in their own field and
coupling normalization, see [BM, eqs. (3.72)–(3.76)].

The one-loop Yang–Mills beta function used in this comparison is derived in
[GW] and [P]. In the matching coupling and Casimir conventions its coefficient
is b₀ = 11 C_g/(48π²). Its numerical value cancels from the trace amplitude:
this check alone does not independently test the factor 11 C_g/(48π²).
The submission's separate effective-coupling theorem, described in §7.4 of
the assessment, specifies that coefficient. The `LeadingTrace` target and
the example below do not add an independent check of that theorem.

References for this calculation:

* [OP] H. Osborn and A. C. Petkou, “Implications of conformal invariance in
  field theories for general dimensions,” Ann. Phys. 231 (1994), 311–362,
  eq. (5.15). https://arxiv.org/abs/hep-th/9307010
* [ZC] M. F. Zoller and K. G. Chetyrkin, “OPE of the energy-momentum tensor
  correlator in massless QCD,” JHEP 12 (2012), 119, eq. (4.3).
  https://arxiv.org/abs/1209.1516
* [BM] M. Bochicchio and S. P. Muscinelli, “Ultraviolet asymptotics of
  glueball propagators,” JHEP 08 (2013), 064, eqs. (3.72)–(3.76).
  https://arxiv.org/abs/1304.6409
* [GW] D. J. Gross and F. Wilczek, “Ultraviolet Behavior of Non-Abelian
  Gauge Theories,” Phys. Rev. Lett. 30 (1973), 1343–1346.
  https://doi.org/10.1103/PhysRevLett.30.1343
* [P] H. D. Politzer, “Reliable Perturbative Results for Strong
  Interactions?,” Phys. Rev. Lett. 30 (1973), 1346–1349.
  https://doi.org/10.1103/PhysRevLett.30.1346
-/

theorem radial_identification (x : SpaceTime) (hx : x ≠ 0) :
    YMAFBridge.K₂ F x = (TraceExtension.euclidean F ‖x‖).re :=
  YMAFBridge.K₂_radial F hx

theorem coefficient_is_fixed (hg : g.IsSimple) :
    Trace.Verse.award g.core = 3 * (g.core.lieDim : ℝ) / Real.pi ^ 4 :=
  YMAFBridge.canonical_award (YangMills.GaugeGroup.coreSimple hg)

/-!
## 6. Read the short adapter from the source estimate to the review target

The hypothesis `ht` is the source's trace-test result for this *same* `F`.
Its `shortDistance` field gives the complex time-axis limit. Its `positive`
field gives positivity of `award`. In the actual combined proof, these come
from the joint construction's `hcore.trace`; they are not additional physical
assumptions, nor are they obtained by choosing a second existence witness.

The proof below displays the adapter's elementary steps. The filter `𝓝[≠] 0`
means all nonzero four-dimensional displacements tending to zero. `uvLog 1 x`
is log(1/|x|) in the fixed reference units. Taking Λ = 1 here does not identify
an intrinsic physical Λ parameter or prove a two-loop correction.
-/

theorem leading_from_source (hg : g.IsSimple)
    (ht : Integration.ManuscriptTraceTests.Tests.{0,0} F
      (YangMills.GaugeGroup.coreSimple hg)) : Acceptance.LeadingTrace F := by
  -- First fix the coefficient and its sign using the source normalization.
  have hp : 0 < 3 * (g.core.lieDim : ℝ) / Real.pi ^ 4 := by
    rw [← coefficient_is_fixed hg]
    exact ht.positive
  have hl : Tendsto (fun x : SpaceTime =>
      YMAFBridge.K₂ F x * ‖x‖ ^ 8 * uvLog 1 x ^ 2)
      (𝓝[≠] 0) (𝓝 (3 * (g.core.lieDim : ℝ) / Real.pi ^ 4)) := by
    -- Compose the positive-distance limit with x ↦ ‖x‖, then take real parts.
    have h := (Complex.continuous_re.tendsto _).comp
      (ht.shortDistance.comp (tendsto_norm_nhdsNE_zero (E := SpaceTime)))
    rw [coefficient_is_fixed hg] at h
    -- At nonzero separation the radial source kernel is the selected K₂.
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [YMAFBridge.K₂_radial F hx]
    simp only [Function.comp_apply, uvLog, one_mul, one_div,
      Complex.smul_re, smul_eq_mul]
    ring
  -- Package both the explicit coefficient and the group's existential predicate.
  exact ⟨hp, hl, ⟨3 * (g.core.lieDim : ℝ) / Real.pi ^ 4, 1,
    hp, by norm_num, hl⟩⟩

/-!
## 7. The joint existence witness already supplies this check

This final projection makes the quantifiers visible. The family `C` is chosen
before the requested extraction order `p`. One refinement `q`, one mixed table
`S`, and one witness `F` satisfy `Accepted` and hence its `LeadingTrace` clause.
The family and phase are not selected afresh for the short-distance test.

The extra conjunction is for exposition: it is already contained in
`Accepted.trace_uv`. This theorem is not a stronger acceptance specification.
-/

theorem constructed_with_trace (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (b : ℝ) (hb : 0 < b) :
    ∃ C : Family g.core, C.path.levels.clock.kernel.penalty = b ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Spec.Final C (p.refine q) S),
        Acceptance.Accepted hg F ∧ Acceptance.LeadingTrace F := by
  obtain ⟨C, hpenalty, horders⟩ := Acceptance.combined_acceptance g hg b hb
  refine ⟨C, hpenalty, fun p => ?_⟩
  obtain ⟨q, S, F, h⟩ := horders p
  exact ⟨q, S, F, h, h.trace_uv⟩

/-!
## Limits of this example

The pointwise statements concern separated insertions and approach the
short-distance singularity without assigning it a physical value at x = 0.
The lattice-origin lemma uses tests supported away from coincidence. The OS
bridge separately integrates against joint Schwartz tests flat on coincidence
diagonals. Those tests cannot determine contact terms supported on the diagonals.

The positive leading coefficient excludes an identically zero trace correlator.
It does not by itself exclude every generalized free field or every composite
of Gaussian fields, establish all-orders perturbative matching, determine an
intrinsic reference mass, or settle the vacuum structure. The lattice, field,
Ward and reconstruction checks must be read together with this observable test.
-/

end YMReview.Examples.LeadingTrace

#print axioms YMReview.Examples.LeadingTrace.selected_state_is_fixed
#print axioms YMReview.Examples.LeadingTrace.centering_uses_the_phase_mean
#print axioms YMReview.Examples.LeadingTrace.centered_one_point
#print axioms YMReview.Examples.LeadingTrace.two_point_is_selected_kernel
#print axioms YMReview.Examples.LeadingTrace.separated_kernel_is_real
#print axioms YMReview.Examples.LeadingTrace.source_and_OS_fields_agree
#print axioms YMReview.Examples.LeadingTrace.centered_trace_has_mixed_lattice_origin
#print axioms YMReview.Examples.LeadingTrace.mixed_expectations_are_phase_averages
#print axioms YMReview.Examples.LeadingTrace.radial_identification
#print axioms YMReview.Examples.LeadingTrace.coefficient_is_fixed
#print axioms YMReview.Examples.LeadingTrace.leading_from_source
#print axioms YMReview.Examples.LeadingTrace.constructed_with_trace
