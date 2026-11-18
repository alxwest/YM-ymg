import ExcitationFromConstructed

/-! Audit the new consequence, including all original source lemmas
reachable through the proof. No sorryAx or extra physical axiom is allowed. -/
#print axioms YangMills.selected_nonvacuum_of_positive_trace
#print axioms YangMills.selected_constructed_word_outside_vacuum

-- Expose the exact hypotheses as well as the axiom dependencies.
#check YangMills.selected_nonvacuum_of_positive_trace
#check YangMills.selected_constructed_word_outside_vacuum
