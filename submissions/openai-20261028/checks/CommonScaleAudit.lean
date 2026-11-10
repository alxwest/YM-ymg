import YM.Spec.Closed

/-! Consumer consequences for one fixed construction family.
These statements concern the submitted RG normalization, not an independently
defined observable coupling, a scheme-independent Lambda, or IR uniqueness. -/
set_option autoImplicit false
noncomputable section

namespace YMReview.CommonScale
open YM YM.RG

variable {G : Gauge} (C : Family G)

theorem reference_spacing : C.S.a 0 = 1 := C.S.a_zero

theorem physical_side (N p : ℕ) :
    C.S.a N * (C.side N p).val = (C.S.period p).val :=
  C.S.span_side N p

variable (h : C.Makes)
include h

theorem reference_coupling (N p : ℕ) :
    C.path.β N p 0 = C.path.levels.clock.bar :=
  h.wilson.reaches N p

theorem same_reference_coupling (N p M q : ℕ) :
    C.path.β N p 0 = C.path.β M q 0 :=
  (reference_coupling C h N p).trans (reference_coupling C h M q).symm

theorem positive_common_reference :
    ∃ betaRef : ℝ, 0 < betaRef ∧ ∀ N p, C.path.β N p 0 = betaRef :=
  ⟨C.path.levels.clock.bar, C.path.levels.clock.bar_pos,
    reference_coupling C h⟩

theorem shared_kinetic_paths (N p q m : ℕ) (hm : m ≤ N) :
    (C.path.rep N p m).path = (C.path.rep N q m).path :=
  h.wilson.path_shared N p q m hm

theorem normalized_kinetic_metric (N p m : ℕ) (hm : m ≤ N) :
    (C.path.rep N p m).path.metric_zero (C.path.rep N p m).clip :=
  (h.wilson.represents N p m hm).good.paths.metric

theorem normalized_loop_jets (N p m : ℕ) (hm : m ≤ N) :
    (C.path.rep N p m).path.loop_jets :=
  (h.wilson.represents N p m hm).good.paths.loop_normal

theorem normalized_regular_remainders (N p m : ℕ) (hm : m ≤ N) :
    (C.path.rep N p m).activities.RegularFamily (C.path.rep N p m).p :=
  (h.wilson.represents N p m hm).good.labels.regular

theorem reference_insertion (d N p : ℕ) (hN : C.ref d ≤ N) (v : C.label d) :
    ((C.factory d N p).entries (C.ref d)
      ((C.factory d N p).terminal.symm v)).x = v :=
  C.normalized h hN v

theorem same_insertion_readout (d N p M q : ℕ)
    (hN : C.ref d ≤ N) (hM : C.ref d ≤ M) (v : C.label d) :
    ((C.factory d N p).entries (C.ref d)
      ((C.factory d N p).terminal.symm v)).x =
    ((C.factory d M q).entries (C.ref d)
      ((C.factory d M q).terminal.symm v)).x :=
  (reference_insertion C h d N p hN v).trans
    (reference_insertion C h d M q hM v).symm

omit h in
theorem calibrated_reset {o : Extraction.Order} {S : Table C.book}
    (F : Spec.Final C o S) :
    ∃ alpha : ℕ → ℕ → ℝ, ∀ N m p, m < N →
      |C.path.β N p m - C.path.β N p (m+1) - alpha N m| ≤ 1 := by
  obtain ⟨sheet, rolls, protection, delays, bar, wait, ratio, prices, post,
    directed, trail, _, hpath, moves⟩ := F.calibration
  refine ⟨directed.kin.alpha, ?_⟩
  intro N m p hm
  have hd := (moves N m p hm).δ
  change |(C.path.rep N p m).beta - (C.path.rep N p (m+1)).beta -
    directed.kin.alpha N m| ≤ 1
  rw [hpath]
  exact hd

end YMReview.CommonScale

#print axioms YMReview.CommonScale.reference_spacing
#print axioms YMReview.CommonScale.physical_side
#print axioms YMReview.CommonScale.reference_coupling
#print axioms YMReview.CommonScale.same_reference_coupling
#print axioms YMReview.CommonScale.positive_common_reference
#print axioms YMReview.CommonScale.shared_kinetic_paths
#print axioms YMReview.CommonScale.normalized_kinetic_metric
#print axioms YMReview.CommonScale.normalized_loop_jets
#print axioms YMReview.CommonScale.normalized_regular_remainders
#print axioms YMReview.CommonScale.reference_insertion
#print axioms YMReview.CommonScale.same_insertion_readout
#print axioms YMReview.CommonScale.calibrated_reset
