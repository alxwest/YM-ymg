import NonzeroPhysicalObservable

/-! Transfer nonzero selected trace correlations to the actual unselected
lattice limit using reflection positivity, continuity in the character, and
full support of the phase measure. No identification of the two states. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.TwoPointScale
open YM YM.Extraction YM.TraceExtension YM.OS Filter Set MeasureTheory
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {o : Order} {S : Table C.book}
variable (F : Spec.Final C o S)

theorem joined_eq_opposed (r : ℝ) : r • Trace.joined = opposed r := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change r • Table.Pairing.closedUp timeAxis _ _ (Fin.castAdd 1 (0 : Fin 1)) = _
    rw [Table.Pairing.enter]
    apply PiLp.ext
    intro a
    fin_cases a <;> norm_num [Trace.ticking, Table.Pairing.ride, Signed.mirrored,
      opposed, Boundary.place, pairH, Bid.bothH, position, points, basis, timeAxis,
      Fin.snoc, Fin.last, Fin.append, Fin.addCases]
    ring
  · change r • Table.Pairing.closedUp timeAxis _ _ (Fin.natAdd 1 (0 : Fin 1)) = _
    rw [Table.Pairing.leave]
    apply PiLp.ext
    intro a
    fin_cases a <;> norm_num [Trace.ticking, opposed, Boundary.place,
      pairH, Bid.bothH, position, points, basis, timeAxis, Fin.snoc, Fin.last, Fin.append, Fin.addCases]
    ring

def phaseValue (r : ℝ) (i : F.α.space.X) : ℂ :=
  Trace.frontCount (F.α.ensemble i) r (center F)

theorem phaseValue_selected (r : ℝ) :
    phaseValue F r F.α.atPoint = euclidean F r := by
  unfold phaseValue Trace.frontCount euclidean
  rw [joined_eq_opposed]
  rfl

theorem phaseValue_nonneg {r : ℝ} (hr : 0 < r) (i : F.α.space.X) :
    0 ≤ (phaseValue F r i).re := by
  have hi := F.phase.phase.states i
  have respects : (F.α.ensemble i).respects S :=
    fun d => (F.phase.phase.retains i d).symm.le
  obtain ⟨X⟩ := OS.schwinger_ready (a := timeAxis) hi
  have hadj : S.adj F.room.kernel.spin 4 timeAxis (center F) = center F :=
    trace_adj F.phase.transport.conserved F.phase.transport.spin
      F.phase.transport.spots (selected_respects F) (selected_hierarchy F)
  obtain ⟨w, hw⟩ := Trace.gram_value hi.laws respects F.room.kernel.spin X hr (center F) hadj
  change 0 ≤ (Trace.frontCount (F.α.ensemble i) r (center F)).re
  rw [← hw, Complex.ofReal_re]
  exact sq_nonneg _

theorem phaseValue_continuous_and_average {r : ℝ} (hr : 0 < r) :
    Continuous (phaseValue F r) ∧
    (∫ i, phaseValue F r i ∂F.α.space.μ) = Trace.frontCount S r (center F) := by
  let w := Word.realize (Trace.unlabel (center F)) (r • Trace.joined)
  have hw : Word.distinct w :=
    (Word.realized ..).mpr (Work.A05.smul_conf hr Trace.joined_free)
  have hv (i) : phaseValue F r i = (F.α.ensemble i).expect w := by
    rw [Table.readAt]
    exact Trace.unlabel_eq (F.phase.phase.states i).laws
      (fun d => (F.phase.phase.retains i d).symm.le) hr (center F)
  have hc : Continuous (phaseValue F r) := by
    have he : phaseValue F r = fun i =>
        F.α.space.character i (OS.Ground.M F.α.unselected w hw) := by
      funext i
      exact (hv i).trans (OS.Cluster.track F.α.unselected w hw i (F.phase.phase.chosen i))
    rw [he]
    exact F.phase.phase.decomposition.weak _
  refine ⟨hc, ?_⟩
  simp_rw [hv]
  rw [F.α.space.barycenter F.α.ensemble F.phase.phase.decomposition
    F.phase.phase.chosen F.room.kernel.translations w hw, Table.readAt]
  exact (Trace.unlabel_eq F.room.kernel.laws (fun _ => le_rfl) hr (center F)).symm

theorem unselected_positive_of_selected {r : ℝ} (hr : 0 < r)
    (hp : 0 < (euclidean F r).re) :
    0 < (Trace.frontCount S r (center F)).re := by
  letI := F.phase.phase.decomposition.normalized
  letI := F.phase.phase.decomposition.support
  obtain ⟨hc, hav⟩ := phaseValue_continuous_and_average F hr
  have hint := hc.integrable_of_hasCompactSupport
    (μ := F.α.space.μ) (HasCompactSupport.of_compactSpace _)
  have hpos := integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp hc) hint.re (phaseValue_nonneg F hr)
    (x := F.α.atPoint) (by
      change (phaseValue F r F.α.atPoint).re ≠ 0
      rw [phaseValue_selected]; exact hp.ne')
  change 0 < ∫ i, (phaseValue F r i).re ∂F.α.space.μ at hpos
  have hread : (∫ i, (phaseValue F r i).re ∂F.α.space.μ) =
      (∫ i, phaseValue F r i ∂F.α.space.μ).re := integral_re hint
  rw [hread, hav] at hpos
  exact hpos

theorem selected_positive_somewhere (hG : G.Simple)
    (h : Integration.ManuscriptTraceTests.Tests F hG) :
    ∃ r : ℝ, 0 < r ∧ 0 < (euclidean F r).re := by
  have ht := (Complex.continuous_re.tendsto _).comp h.shortDistance
  have hp := ht.eventually (lt_mem_nhds (by
    simpa only [Complex.ofReal_re] using h.positive))
  obtain ⟨r, hp, hr⟩ := (hp.and
    (self_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioi 0)).exists
  refine ⟨r, hr, ?_⟩
  simp only [Function.comp_apply, Complex.smul_re, smul_eq_mul] at hp
  by_contra hn
  have hw : 0 ≤ r^8 * (Real.log r⁻¹)^2 := by positivity
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_gt hn))) hp

theorem nonzero_unselected_two_point (hG : G.Simple)
    (h : Integration.ManuscriptTraceTests.Tests F hG) :
    ∃ t : Test 2, t.applyTo (fun x => S.read x (Trace.unlabel (center F))) ≠ 0 := by
  obtain ⟨r, hr, hp⟩ := selected_positive_somewhere F hG h
  have hu := unselected_positive_of_selected F hr hp
  by_contra! hn
  have hz := (Test.weak_null
    (S.smooth_read F.room.kernel.smooth (Trace.unlabel (center F))).continuousOn).mp hn
  have hx : r • Trace.joined ∈ conf 2 := Work.A05.smul_conf hr Trace.joined_free
  have he := hz hx
  change S.read (r • Trace.joined) (Trace.unlabel (center F)) = 0 at he
  rw [← Trace.unlabel_eq F.room.kernel.laws (fun _ => le_rfl) hr (center F)] at he
  rw [he, Complex.zero_re] at hu
  exact (lt_irrefl 0) hu

/-- A fixed separated two-point probe has a positive finite correlation-root
limit. Centering and the probe may depend on F, but neither varies with N,p.
The physical interpretation as a mass uses dimension-four trace fields and a
joint smearing density; no intrinsic scale or spectral gap is asserted. -/
def MassLimit : Prop :=
  ∃ (t : Test 2) (M : ℝ), 0 < M ∧
    (Order.mk Sequence.full o.per).limits (fun p => suitable C.S p t)
      (fun N p => NonzeroScale.massMagnitude 8
        (Order.smears C N p (Trace.unlabel (center F)) t)) M

theorem mass_limit (hG : G.Simple)
    (h : Integration.ManuscriptTraceTests.Tests F hG)
    (huv : (Order.mk Sequence.full o.per).Ordered C S) : MassLimit F := by
  obtain ⟨t, ht⟩ := nonzero_unselected_two_point F hG h
  refine ⟨t, NonzeroScale.massMagnitude 8
    (t.applyTo (fun x => S.read x (Trace.unlabel (center F)))),
    NonzeroScale.massMagnitude_pos 8 ht, ?_⟩
  exact NonzeroScale.map_limits (huv.reads 2 (Trace.unlabel (center F)) t)
    (NonzeroScale.continuous_massMagnitude 8)

/-- One actual submitted family, chosen before the requested extraction order.
No additional extraction is introduced to make the mass proxy converge. -/
theorem constructed (hG : G.Simple) {b : ℝ} (hb : 0 < b) :
    ∃ C : Family G, ∀ p : Order,
      ∃ (q : Order) (S : Table C.book) (F : Spec.Final C (p.refine q) S),
        MassLimit F := by
  obtain ⟨_, H⟩ := Nonperturbative.continuum.{0,0} hG hb
  refine ⟨(Independent.fundedRun hG hb).family, ?_⟩
  intro p
  obtain ⟨q, S, F, L, Q, M, huv, _, core, _⟩ := H p
  exact ⟨q, S, F, mass_limit F hG core.trace huv⟩

end YMReview.TwoPointScale

#print axioms YMReview.TwoPointScale.joined_eq_opposed
#print axioms YMReview.TwoPointScale.phaseValue_selected
#print axioms YMReview.TwoPointScale.phaseValue_nonneg
#print axioms YMReview.TwoPointScale.phaseValue_continuous_and_average
#print axioms YMReview.TwoPointScale.unselected_positive_of_selected
#print axioms YMReview.TwoPointScale.selected_positive_somewhere
#print axioms YMReview.TwoPointScale.nonzero_unselected_two_point

#print axioms YMReview.TwoPointScale.mass_limit
#print axioms YMReview.TwoPointScale.constructed
