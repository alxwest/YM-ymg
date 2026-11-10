import YM.Nonperturbative.Continuum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A nonzero, finite correlation-derived quantity from the actual Wilson
limit, with the full UV mesh and the already chosen IR extraction.

The probe contains the source's centered stress trace and possibly spectator
fields. It is chosen for one Final, not uniformly across all possible Finals.
The mass-dimension interpretation uses the engineering grades and a fixed
joint smearing density. No intrinsic mass, mass gap, or IR uniqueness is claimed.
-/
set_option autoImplicit false
noncomputable section

namespace YMReview.NonzeroScale
open YM YM.Extraction YM.TraceExtension Filter Set MeasureTheory
open scoped Topology BigOperators

def massMagnitude (D : ℕ) (z : ℂ) : ℝ := ‖z‖ ^ ((1 : ℝ) / D)

theorem continuous_massMagnitude (D : ℕ) : Continuous (massMagnitude D) :=
  (Real.continuous_rpow_const (by positivity : 0 ≤ (1 : ℝ) / D)).comp continuous_norm

theorem massMagnitude_pos (D : ℕ) {z : ℂ} (hz : z ≠ 0) :
    0 < massMagnitude D z :=
  Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _

theorem map_limits {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {o : Order} {A : ℕ → Prop} {W : ℕ → ℕ → X} {x : X}
    (h : o.limits A W x) {f : X → Y} (hf : Continuous f) :
    o.limits A (fun N p => f (W N p)) (f x) := by
  obtain ⟨fits, row, uv, ir⟩ := h
  exact ⟨fits, fun p => f (row p),
    fun p hp => (hf.tendsto _).comp (uv p hp), (hf.tendsto _).comp ir⟩

variable {G : Gauge} {L : Register G} {S : Table L}

/-- A field is zero precisely when every tested correlation containing it is
zero. This gives a nonzero unselected correlation without equating phases. -/
theorem nonzero_field_detected (hs : S.Hierarchy) {d : ℕ} (v : S.Field d)
    (hv : v ≠ 0) :
    ∃ (n : ℕ) (w : Fin n → L.Token) (i : Fin n) (t : Test n),
      w i = ⟨d, S.representative d v⟩ ∧
      t.applyTo (fun x => S.read x w) ≠ 0 := by
  classical
  have hn : S.representative d v ∉ S.null d := by
    intro h
    have hp : S.project d (S.representative d v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h
    exact hv ((S.rep d v).symm.trans hp)
  have ht : ¬ S.vanishes d (S.representative d v) :=
    fun h => hn ((S.equivalent hs.smooth hs.laws.toSymmetric d _).mpr h)
  unfold Table.vanishes at ht
  push Not at ht
  obtain ⟨n, w, i, hi, t, ht⟩ := ht
  exact ⟨n, w, i, t, hi, ht⟩

def weight {n : ℕ} (w : Fin n → L.Token) : ℕ := ∑ i, (w i).1

theorem grade_le_weight {n : ℕ} (w : Fin n → L.Token) (i : Fin n) :
    (w i).1 ≤ weight w :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (w j).1) (Finset.mem_univ i)

variable {C : Family G} {o : Order} {T : Table C.book}

/-- Explicit probe data on the same family/table as the lattice limit. -/
structure Probe (F : Spec.Final C o T) where
  n : ℕ
  labels : Fin n → C.book.Token
  traceSlot : Fin n
  trace_label : labels traceSlot = ⟨4, T.representative 4 (center F)⟩
  test : Test n
  nonzero : test.applyTo (fun x => T.read x labels) ≠ 0
  fullUV : (Order.mk Sequence.full o.per).Ordered C T

namespace Probe
variable {F : Spec.Final C o T} (P : Probe F)

def dimension : ℕ := weight P.labels
def value : ℝ := massMagnitude P.dimension (P.test.applyTo (fun x => T.read x P.labels))
def lattice (N p : ℕ) : ℝ := massMagnitude P.dimension (Order.smears C N p P.labels P.test)

theorem dimension_ge_four : 4 ≤ P.dimension := by
  have h := grade_le_weight P.labels P.traceSlot
  rw [P.trace_label] at h
  exact h

theorem positive : 0 < P.value := massMagnitude_pos _ P.nonzero

theorem converges :
    (Order.mk Sequence.full o.per).limits (fun p => suitable C.S p P.test)
      P.lattice P.value :=
  map_limits (P.fullUV.reads P.n P.labels P.test) (continuous_massMagnitude P.dimension)

end Probe

theorem probe_from_trace (F : Spec.Final C o T) (hG : G.Simple)
    (h : Integration.ManuscriptTraceTests.Tests F hG)
    (huv : (Order.mk Sequence.full o.per).Ordered C T) : Nonempty (Probe F) := by
  have hp : center F ≠ 0 := by
    intro hz
    apply TraceExtension.nonzero_strength F h.positive h.shortDistance
    simp [pinned, hz]
  obtain ⟨n, w, i, t, hi, ht⟩ := nonzero_field_detected F.room.kernel (center F) hp
  exact ⟨⟨n, w, i, hi, t, ht, huv⟩⟩

/-- Instantiation on the submitted construction, preserving its one family
before the requested IR order. The probe can depend on the resulting Final. -/
theorem constructed (hG : G.Simple) {b : ℝ} (hb : 0 < b) :
    ∃ C : Family G, ∀ p : Order,
      ∃ (q : Order) (T : Table C.book) (F : Spec.Final C (p.refine q) T),
        Nonempty (Probe F) := by
  obtain ⟨_, H⟩ := Nonperturbative.continuum.{0,0} hG hb
  refine ⟨(Independent.fundedRun hG hb).family, ?_⟩
  intro p
  obtain ⟨q, T, F, L, Q, M, huv, _, core, _⟩ := H p
  exact ⟨q, T, F, probe_from_trace F hG core.trace huv⟩

end YMReview.NonzeroScale

#print axioms YMReview.NonzeroScale.nonzero_field_detected
#print axioms YMReview.NonzeroScale.Probe.dimension_ge_four
#print axioms YMReview.NonzeroScale.Probe.positive
#print axioms YMReview.NonzeroScale.Probe.converges
#print axioms YMReview.NonzeroScale.probe_from_trace
#print axioms YMReview.NonzeroScale.constructed
