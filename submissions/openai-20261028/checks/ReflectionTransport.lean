import Invariance
import YM.Euclid.Pairing

/-! Transport of compact ordered Schwartz tests and the centered trace into
exactly the selected state's compact-test reflection-positive form. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM YM.Table MeasureTheory Set
open scoped Topology BigOperators ContDiff

/-- Swapping the time coordinate and passing to Euclidean coordinates has
unit Jacobian, including the zero-arity product below. -/
theorem pointEquiv_measurePreserving : MeasurePreserving pointEquiv := by
  have h : MeasurePreserving (fun x : Fin 4 → ℝ => x ∘ axisSwap) :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) axisSwap).symm
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) axisSwap)
  exact (PiLp.volume_preserving_toLp (Fin 4)).comp h

theorem configEquiv_measurePreserving (n : ℕ) : MeasurePreserving (configEquiv n) := by
  have h := (Points.volume_product n).symm
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)).toHomeomorph.toMeasurableEquiv
  exact h.comp (volume_preserving_pi (fun _ : Fin n => pointEquiv_measurePreserving))

theorem ordered_config_conf {n : ℕ} {x : NPointDomain 3 n}
    (hx : x ∈ OrderedPositiveTimeRegion 3 n) : configEquiv n x ∈ conf n := by
  apply (configEquiv_conf x).mpr
  intro i j hij
  by_contra hne
  exact not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion hx ⟨i, j, hne, hij⟩

/-- The same compact test, expressed in the submitted construction's coordinates. -/
def compactTest {n : ℕ} (f : SchwartzNPoint 3 n) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ OrderedPositiveTimeRegion 3 n) : Test n where
  toFun x := f ((configEquiv n).symm x)
  contDiff' := f.smooth'.comp (configEquiv n).symm.contDiff
  hasCompactSupport' := hc.comp_homeomorph (configEquiv n).symm.toHomeomorph
  tsupport_subset' := by
    intro x hx
    have hh := hf (tsupport_comp_subset_preimage f (configEquiv n).symm.continuous hx)
    change x ∈ conf n
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using ordered_config_conf hh

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- Constant centered-trace labels on the transported compact test. -/
def tracePastTest {n : ℕ} (f : SchwartzNPoint 3 n) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ OrderedPositiveTimeRegion 3 n) : PastTest C.book timeAxis where
  n := n
  v _ := ⟨4, S.representative 4 (Trace.traceField F)⟩
  f := compactTest f hc hf
  past x hx := by
    have hh := hf (tsupport_comp_subset_preimage f (configEquiv n).symm.continuous hx)
    intro i
    have he := pointEquiv_time (((configEquiv n).symm x) i)
    have hx' := congrArg (fun y : Points n => y i timeAxis)
      ((configEquiv n).apply_symm_apply x)
    exact hx' ▸ (he.symm ▸ (hh i).1)

/-- The representative's reflected label equals the original label in the
quotient respected by this same selected phase. -/
theorem trace_reflected_project :
    S.project 4 (C.book.adj 4 timeAxis (S.representative 4 (Trace.traceField F))) =
      S.project 4 (S.representative 4 (Trace.traceField F)) := by
  rw [← S.adj_project F.room.kernel.spin, S.rep]
  exact Trace.theta_adjoint F _


/-- Reading the reflected and unreflected representative labels gives precisely
our scalar kernel on separated configurations, with no change of state. -/
theorem trace_tied_read {n m : ℕ} (x : Points (n + m)) (hx : x ∈ conf (n + m)) :
    (Trace.state F).read x
      (Pairing.tied
        (fun _ : Fin n => (⟨4, S.representative 4 (Trace.traceField F)⟩ : C.book.Token))
        (fun _ : Fin m => (⟨4, S.representative 4 (Trace.traceField F)⟩ : C.book.Token))
        timeAxis) = scalarKernel F (n + m) x := by
  rw [← S.at_project (Trace.state F)
    (F.phase.phase.states F.α.atPoint).laws.toSymmetric (Trace.fits F) hx]
  change S.useAt (Trace.state F) x _ = S.useAt (Trace.state F) x _
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply, Pairing.tied, Fin.append_left, Register.reflectedToken]
    dsimp only [Table.classTokens]
    rw [trace_reflected_project F, S.rep]
  · intro j
    simp only [Function.comp_apply, Pairing.tied, Fin.append_right]
    dsimp only [Table.classTokens]
    rw [S.rep]

theorem configEquiv_earlier {n m : ℕ} (x : NPointDomain 3 (n + m)) :
    Pairing.earlier timeAxis (configEquiv (n + m) x) =
      configEquiv n (timeReflectionN 3 (splitFirst n m x)) := by
  apply PiLp.ext
  intro i
  exact (pointEquiv_reflection (x (Fin.castAdd m i))).symm

theorem configEquiv_after {n m : ℕ} (x : NPointDomain 3 (n + m)) :
    Pairing.after (configEquiv (n + m) x) = configEquiv m (splitLast n m x) := rfl

/-- Pointwise agreement of the two reflection/conjugation and tensor conventions. -/
theorem trace_withOther_apply {n m : ℕ} (f : SchwartzNPoint 3 n) (g : SchwartzNPoint 3 m)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf : tsupport f ⊆ OrderedPositiveTimeRegion 3 n)
    (hg : tsupport g ⊆ OrderedPositiveTimeRegion 3 m) (x : NPointDomain 3 (n + m)) :
    Pairing.withOther (tracePastTest F f hfc hf) (tracePastTest F g hgc hg)
      (configEquiv (n + m) x) = f.osConjTensorProduct g x := by
  change star (f ((configEquiv n).symm (Pairing.earlier timeAxis (configEquiv (n + m) x)))) *
    g ((configEquiv m).symm (Pairing.after (configEquiv (n + m) x))) = _
  rw [configEquiv_earlier, configEquiv_after, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Equality of each matrix entry, before taking finite sums or a limit. -/
theorem compact_reflection_entry {n m : ℕ} (f : SchwartzNPoint 3 n) (g : SchwartzNPoint 3 m)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf : tsupport f ⊆ OrderedPositiveTimeRegion 3 n)
    (hg : tsupport g ⊆ OrderedPositiveTimeRegion 3 m) :
    schwinger F (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) =
      ∫ z, (Trace.state F).smeared timeAxis
        (tracePastTest F f hfc hf) (tracePastTest F g hgc hg) z := by
  let Q := tracePastTest F f hfc hf
  let V := tracePastTest F g hgc hg
  rw [schwinger_eq_selected_integral,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        f g hf hg)]
  calc
    _ = ∫ x : NPointDomain 3 (n + m),
        Pairing.withOther Q V (configEquiv (n + m) x) *
          scalarKernel F (n + m) (configEquiv (n + m) x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [trace_withOther_apply F f g hfc hgc hf hg x]
      exact mul_comm _ _
    _ = (Pairing.withOther Q V).applyTo (scalarKernel F (n + m)) :=
      (configEquiv_measurePreserving (n + m)).integral_comp
        (configEquiv (n + m)).toHomeomorph.measurableEmbedding
        (fun x : Points (n + m) => Pairing.withOther Q V x * scalarKernel F (n + m) x)
    _ = (Pairing.withOther Q V).applyTo
        (fun x => (Trace.state F).read x (Pairing.tied Q.v V.v timeAxis)) := by
      apply Test.apply_eq
      intro x hx
      exact (trace_tied_read F x hx).symm
    _ = _ := Pairing.at_integral (Trace.state F)
      (F.phase.phase.states F.α.atPoint).laws.toSymmetric
      (F.phase.phase.states F.α.atPoint).smooth Q V

end YMOSBridge
