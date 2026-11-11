import PublicView
import YM.TraceExtension.Sundial.Grand
import ExcitationFromPublic

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YangMills
open YM YM.Spec YM.TraceExtension

/-!
# The constructed selected stress trace produces non-vacuum states

This uses the original construction's `Spec.Final`, selected physical
`view F.action`, `pinned_centered`, field faithfulness, and
`nonzero_strength`. No field-label nonzero hypothesis or separate
Wightman witness is supplied.

The only analytic inputs, positivity and `EuclideanAsymptotic F A`,
are exactly the positive short-distance limit retained in the original
construction's trace conclusions. This module does not rebuild that
construction's global existence theorem and does not assert a mass gap.
-/

variable {G : Gauge} {C : Family G} {p : Extraction.Order}
  {S : Table C.book}

/-- The SAME selected Wightman theory in the original final construction
has a field-generated state outside its vacuum line whenever its actual
centered trace has the positive short-distance asymptotic. The source's
own `nonzero_strength` discharges nonzero trace, and its own
`pinned_centered` discharges the vacuum one-point identity. -/
theorem selected_nonvacuum_of_positive_trace
    (F : Final C p S) {A : ℝ} (hA : 0 < A)
    (hshort : EuclideanAsymptotic F A) :
    (view F.action).HasFieldExcitation := by
  apply (view F.action).hasFieldExcitation_of_centered_nonzero
    (view_axioms F.action F.realization.qt) (pinned F)
  · intro test
    exact pinned_centered F test
  · exact F.realization.qt.faithful (pinned F)
      (nonzero_strength F hA hshort)

/-- Unfold the public packaging: the excited word is literally a word
of the original constructed operators on the original selected Hilbert
space, not an auxiliary model or a differently chosen phase. -/
theorem selected_constructed_word_outside_vacuum
    (F : Final C p S) {A : ℝ} (hA : 0 < A)
    (hshort : EuclideanAsymptotic F A) :
    ∃ word : List (S.Union × TestFunction),
      F.action.operators.vector word ∉
        Submodule.span ℂ {F.action.operators.vacuum} := by
  obtain ⟨word, hword⟩ := selected_nonvacuum_of_positive_trace F hA hshort
  refine ⟨word, ?_⟩
  change ((fieldsOf F.action).vector word).1 ∉
    Submodule.span ℂ {F.action.operators.vacuum} at hword
  rw [vector_eq] at hword
  exact hword

end YangMills
