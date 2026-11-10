import ReflectionTransport
import ImportedReflectionApproximation

/-! E2 for the same selected phase and centered stress trace as E0/E1/E3.
The compact reflection form is identified entry by entry, then its positivity
extends in the Schwartz topology while retaining ordered positive-time support. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM YM.Table MeasureTheory Set YangMills.OSRecon
open scoped Topology BigOperators ComplexOrder
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- Compact-test positivity on the target's exact reflection form, in arbitrary
mixed arities with arbitrary complex coefficients (including arity zero). -/
theorem compact_reflection_positive
    (N : ℕ) (degree : Fin N → ℕ) (h : ∀ i, SchwartzNPoint 3 (degree i))
    (hc : ∀ i, HasCompactSupport (h i))
    (hh : ∀ i, tsupport (h i) ⊆ OrderedPositiveTimeRegion 3 (degree i))
    (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, star (c i) * c j * schwingerCLM F (degree i + degree j)
      (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j)))).re := by
  have hpos := (F.phase.phase.states F.α.atPoint).onTests.2 timeAxis N
    (fun i => tracePastTest F (h i) (hc i) (hh i)) c
  have hentry (i j : Fin N) :
      schwingerCLM F (degree i + degree j)
        (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j))) =
      ∫ z, (Trace.state F).smeared timeAxis
        (tracePastTest F (h i) (hc i) (hh i))
        (tracePastTest F (h j) (hc j) (hh j)) z :=
    compact_reflection_entry F (h i) (h j) (hc i) (hc j) (hh i) (hh j)
  simpa only [hentry] using (Complex.nonneg_iff.mp hpos).1

/-- Positivity extends to all ordered-support Schwartz test families by
support-preserving compact cutoffs and continuity of E0 and reflected tensors. -/
theorem reflection_positive_family
    (N : ℕ) (degree : Fin N → ℕ) (h : ∀ i, SchwartzNPoint 3 (degree i))
    (hh : ∀ i, tsupport (h i) ⊆ OrderedPositiveTimeRegion 3 (degree i))
    (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, star (c i) * c j * schwingerCLM F (degree i + degree j)
      (ZeroDiagonalSchwartz.ofClassical ((h i).osConjTensorProduct (h j)))).re :=
  source_reflection_positive_of_compact (schwingerCLM F)
    (compact_reflection_positive F) degree h hh c

/-- The literal OSreconstruction E2 field for every Borchers sequence allowed by
that axiom, not merely finite tensor-product or compact-support tests. -/
theorem E2_reflection_positive (B : BorchersSequence 3)
    (hB : ∀ n, tsupport (B.funcs n : NPointDomain 3 n → ℂ) ⊆
      OrderedPositiveTimeRegion 3 n) :
    (OSInnerProduct 3 (schwinger F) B B).re ≥ 0 :=
  source_OSInnerProduct_nonneg_of_family (schwingerCLM F)
    (reflection_positive_family F) B hB

#print axioms compact_reflection_positive
#print axioms reflection_positive_family
#print axioms E2_reflection_positive
end YMOSBridge
