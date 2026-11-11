import ChallengeSpec

set_option autoImplicit false
noncomputable section
namespace YangMills

/-!
# Non-vacuum field excitation in the October Wilson Wightman reconstruction

This is a source-native consequence of the actual normalized, cyclic
Wightman field system, not an assumption about a mass gap or the spectrum.

The public challenge's `Reconstructed.acts` is insufficient by itself:
a nonzero identity operator would also satisfy it. A *centered nonzero*
field, by contrast, forces a vacuum word outside the vacuum line.
-/

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- There is an actual finite smeared field word whose state is not on the
vacuum ray in the reconstructed physical Hilbert space. -/
def WightmanTheory.HasFieldExcitation (Q : WightmanTheory H Labels) : Prop :=
  ∃ word : List (Labels.carrier × TestFunction),
    (Q.fields.vector word : H.carrier) ∉
      Submodule.span ℂ {(Q.fields.vacuum : H.carrier)}

/-- A centered nonzero physical smeared field creates a non-vacuum state
through cyclicity. No positive spectral gap, phase uniqueness, lattice
probe, or IR mass estimate is assumed. -/
theorem WightmanTheory.hasFieldExcitation_of_centered_nonzero
    (Q : WightmanTheory H Labels) (hQ : Q.Axioms)
    (label : Labels.carrier)
    (centered : ∀ f : TestFunction,
      inner ℂ (Q.fields.vacuum : H.carrier)
        (Q.fields.field label f Q.fields.vacuum : H.carrier) = 0)
    (nonzero : ∃ f : TestFunction, Q.fields.field label f ≠ 0) :
    Q.HasFieldExcitation := by
  obtain ⟨f, hf⟩ := nonzero
  by_contra hnot
  have allWord : ∀ word : List (Labels.carrier × TestFunction),
      (Q.fields.vector word : H.carrier) ∈
        Submodule.span ℂ {(Q.fields.vacuum : H.carrier)} := by
    simpa [WightmanTheory.HasFieldExcitation] using hnot
  have hspan : Submodule.span ℂ
      (Set.range (fun word : List (Labels.carrier × TestFunction) =>
        (Q.fields.vector word : H.carrier))) ≤
      Submodule.span ℂ {(Q.fields.vacuum : H.carrier)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨word, rfl⟩
    exact allWord word
  have allVacuum (v : Q.fields.domain) :
      ∃ c : ℂ, c • (Q.fields.vacuum : H.carrier) = (v : H.carrier) := by
    apply Submodule.mem_span_singleton.mp
    apply hspan
    rw [← hQ.w1.domain.cyclicVacuum]
    exact v.property
  have hvac : (Q.fields.vacuum : H.carrier) ≠ 0 := by
    intro hz
    have hn := hQ.w1.domain.normalizedVacuum
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hinner : inner ℂ (Q.fields.vacuum : H.carrier)
      (Q.fields.vacuum : H.carrier) ≠ 0 := inner_self_ne_zero.mpr hvac
  obtain ⟨c, hc⟩ := allVacuum (Q.fields.field label f Q.fields.vacuum)
  have hczero : c = 0 := by
    have heq := congrArg
      (fun x : H.carrier => inner ℂ (Q.fields.vacuum : H.carrier) x) hc
    rw [inner_smul_right, centered f] at heq
    exact (mul_eq_zero.mp heq).resolve_right hinner
  have hfieldvac : Q.fields.field label f Q.fields.vacuum = 0 := by
    apply Subtype.ext
    change (Q.fields.field label f Q.fields.vacuum : H.carrier) = 0
    calc
      _ = c • (Q.fields.vacuum : H.carrier) := hc.symm
      _ = 0 := by simp [hczero]
  have hfieldzero : Q.fields.field label f = 0 := by
    apply LinearMap.ext
    intro v
    obtain ⟨a, ha⟩ := allVacuum v
    have hv : v = a • Q.fields.vacuum := Subtype.ext ha.symm
    simp only [LinearMap.zero_apply]
    rw [hv, map_smul, hfieldvac, smul_zero]
  exact hf hfieldzero


/-!
# Source-native bridge from the October public hierarchy

This lemma uses the ACTUAL `Hierarchy`, `Reconstructed` and `TraceTest`
declarations from the October Wilson submission. It does not need a mass
gap, a unique IR limit, or the all-orders perturbative coefficients.

The explicit `centeredTrace ≠ 0` hypothesis must be discharged using
the submitted construction's trace nonzero theorem. Its `TraceTest`
alone does not declare `centeredTrace ≠ 0` as a field.
-/

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The selected physical Wightman theory has a non-vacuum field word if
its reconstructed centered trace is nonzero in its graded field space.
All data refer to ONE `Hierarchy`, not a separate trace or phase. -/
theorem Hierarchy.nonvacuum_of_reconstructed_nonzero_trace
    (T : Hierarchy C) (r : T.Reconstructed)
    (trace : T.TraceTest) (htrace : T.centeredTrace ≠ 0) :
    T.theory.HasFieldExcitation := by
  have hlabel : T.toLabel 4 T.centeredTrace ≠ 0 := by
    intro heq
    apply htrace
    apply r.injective 4
    simpa using heq
  exact T.theory.hasFieldExcitation_of_centered_nonzero r.axioms
    (T.toLabel 4 T.centeredTrace) trace.centered (r.faithful _ hlabel)

end YangMills
