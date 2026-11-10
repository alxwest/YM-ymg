import YM.Spec.Closed
import YM.Next.MAXWELL.System
import YM.EveryPhase.Extension

/-!
Consumer audit of operator content. These consequences do not assert an
identification with an independently defined canonical Yang--Mills Hilbert space.
The equivalences below are complex linear equivalences, not algebra isomorphisms
or charge-conjugation-equivariant identifications.
-/
set_option autoImplicit false
noncomputable section
namespace YMReview.OperatorCompleteness
open YM YM.Analysis YM.Boundary
open scoped Topology

variable {G : Gauge}

/-- Every gauge-invariant polynomial belongs to some finite register level. -/
theorem raw_register_exhaustive (p : Labels.Pol G)
    (hp : p ∈ Labels.invariantSpace G) :
    ∃ d : ℕ, ∃ v : Labels.Label G d, v.val = p := by
  classical
  refine ⟨p.support.sup Labels.height, ⟨p, ?_, hp⟩, rfl⟩
  change p ∈ MvPolynomial.restrictSupport ℂ {m | Labels.height m ≤ _}
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  exact Finset.le_sup (f := (Labels.height : (Labels.Key G →₀ ℕ) → ℕ)) hm

/-- The free comparison space has no further separated-correlator nulls. -/
theorem free_no_extra_nulls (d : ℕ) : Maxwell.residual G d = ⊥ :=
  Maxwell.Free.no_residual G d

/-- Its on-shell image is exactly the full invariant polynomial space at this weight. -/
theorem free_sector_exhaustive (d : ℕ) (p : Maxwell.WickPol G) :
    p ∈ Maxwell.shellSector G d ↔
      p ∈ Maxwell.Free.lowerCap G d ∧ ∀ u : G.El, Maxwell.Free.pigment u p = p :=
  Maxwell.Free.sector

variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C f S)

include F in
/-- Combining the submitted rank theorem with the exact free quotient. -/
theorem local_field_content (d : ℕ) :
    Nonempty (S.Field d ≃ₗ[ℂ] ↥(Maxwell.shellSector G d)) := by
  obtain ⟨_, hr⟩ := F.phase.transport.comparator
  obtain ⟨e, _, _⟩ := hr d
  exact ⟨e.trans (Maxwell.Free.fields C.book.grid d)⟩

/-- Phase selection preserves this full degreewise field content. -/
theorem phase_field_content (i : F.α.space.X) (d : ℕ) :
    Nonempty ((F.α.ensemble i).Field d ≃ₗ[ℂ] ↥(Maxwell.shellSector G d)) := by
  obtain ⟨e⟩ := local_field_content F d
  exact ⟨(Submodule.quotEquivOfEq _ _ (F.phase.phase.retains i d)).trans e⟩

/-- All registered words, not just stress-trace words, generate the selected space. -/
theorem registered_words_dense :
    Dense ((Submodule.span ℂ (Set.range F.action.operators.vector) :
      Submodule ℂ F.action.operators.H) : Set F.action.operators.H) := by
  rw [← F.realization.qt.total.cyclic]
  exact F.realization.qt.total.everywhere

/-- Every nonzero local quotient field has a nonzero smeared operator. -/
theorem quotient_fields_not_lost (p : S.Union) (hp : p ≠ 0) :
    ∃ g : Test4, F.action.operators.field p g ≠ 0 :=
  F.realization.qt.faithful p hp

end YMReview.OperatorCompleteness

#print axioms YMReview.OperatorCompleteness.raw_register_exhaustive
#print axioms YMReview.OperatorCompleteness.free_no_extra_nulls
#print axioms YMReview.OperatorCompleteness.free_sector_exhaustive
#print axioms YMReview.OperatorCompleteness.local_field_content
#print axioms YMReview.OperatorCompleteness.phase_field_content
#print axioms YMReview.OperatorCompleteness.registered_words_dense
#print axioms YMReview.OperatorCompleteness.quotient_fields_not_lost
#print axioms YM.EveryPhase.recognizes
