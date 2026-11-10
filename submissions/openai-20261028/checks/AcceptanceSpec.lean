import CompleteOS
import AFSourceBridge
import CommonScaleAudit
import TwoPointPhysicalObservable
import CompletenessAudit
import WardFormulationAudit
import LGTWilsonBridge
import Construction

/-!
# Combined acceptance target for the verified scope

This statement binds ONE Wilson family C, ONE extracted table S and ONE Final F.
The selected scalar OS family, UV trace and translation tensor are fixed by F.
The Wilson limit is the unselected table; the phase-average clause relates it
to the selected theory without identifying the selected state with the mixture.

This is a proposed acceptance specification, not a record of human signoff.
IR uniqueness, intrinsic scale setting, two-loop/all-orders matching, SD1--SD4,
contact/dilation Ward identities and improvement uniqueness are not clauses.
Builds, Comparator and Palomar are external checks, not mathematical fields.
-/
set_option autoImplicit false
noncomputable section
namespace YMReview.Acceptance
open YM YM.Table Filter Set MeasureTheory
open scoped Topology BigOperators

variable {g : YangMills.GaugeGroup} {C : Family g.core}
variable {o : Extraction.Order} {S : Table C.book}

/-- The actual finite law and common calibration, with full UV then extracted IR.
The coupling conversion is beta_lgt = beta_submission / representation dimension. -/
structure LatticeAndScale (C : Family g.core) (o : Extraction.Order)
    (S : Table C.book) : Prop where
  makes : C.Makes
  regular : YangMills.WilsonRegularity (YangMills.wilsonFamily C)
  finite_law (N p : ℕ) :
    MeasurePreserving (YMLGTBridge.configEquiv g (C.side N p))
      (ymMeasure g.image (g.n+1) 4 (C.side N p).val
        (C.beta N p / (g.n+1 : ℕ)) Finset.univ)
      (YangMills.wilsonLaw g (C.side N p) (C.beta N p) g.core.probHaar)
  finite_moments (N p : ℕ) {n : ℕ} (v : Fin n → C.book.Token)
    (x : Fin n → Lattice.Site (C.side N p)) :
    (YangMills.wilsonFamily C).finiteMoment N p v x = C.numeric N p v x
  ordered : (Extraction.Order.mk Extraction.Sequence.full o.per).Ordered C S
  public_limit : (YangMills.wilsonFamily C).Converges o.per (fun v x => S.read x v)
  positions_uv : FullVolume.PositionsUV C Extraction.Sequence.full
  reference_spacing : C.S.a 0 = 1
  physical_side (N p : ℕ) : C.S.a N * (C.side N p).val = (C.S.period p).val
  common_coupling : ∃ betaRef : ℝ, 0 < betaRef ∧
    ∀ N p, C.path.β N p 0 = betaRef
  shared_kinetic_paths (N p q m : ℕ) (hm : m ≤ N) :
    (C.path.rep N p m).path = (C.path.rep N q m).path
  insertion_readout (d N p : ℕ) (hN : C.ref d ≤ N) (v : C.label d) :
    ((C.factory d N p).entries (C.ref d)
      ((C.factory d N p).terminal.symm v)).x = v
  calibrated_reset : ∃ alpha : ℕ → ℕ → ℝ, ∀ N m p, m < N →
    |C.path.β N p m - C.path.β N p (m+1) - alpha N m| ≤ 1

/-- Exact group OS interface on the selected centered trace, plus the actual
integral and the phase-average identification with the lattice-limit table. -/
structure PhaseAndOS (F : Spec.Final C o S) : Prop where
  phase_probability : IsProbabilityMeasure F.α.space.μ
  phase_full_support : F.α.space.μ.IsOpenPosMeasure
  phase_average (w : C.book.Word) (hw : Word.distinct w) :
    (∫ i, (F.α.ensemble i).expect w ∂F.α.space.μ) = S.expect w
  os_and_growth : ∃ axioms : OsterwalderSchraderAxioms 3,
    axioms.S = YMOSBridge.schwinger F ∧
    Nonempty (OSArityLinearGrowthCondition 3 axioms)
  normalized (f : ZeroDiagonalSchwartz 3 0) :
    YMOSBridge.schwinger F 0 f = f.1 0
  centered (f : ZeroDiagonalSchwartz 3 1) : YMOSBridge.schwinger F 1 f = 0
  integrable (n : ℕ) (f : ZeroDiagonalSchwartz 3 n) :
    Integrable (fun x : NPointDomain 3 n =>
      (YMOSBridge.targetKernel F n x : ℂ) * f.1 x)
  pairing (n : ℕ) (f : ZeroDiagonalSchwartz 3 n) :
    YMOSBridge.schwinger F n f = ∫ x : NPointDomain 3 n,
      YMOSBridge.scalarKernel F n (YMOSBridge.configEquiv n x) * f.1 x
  same_trace : TraceExtension.center F = Trace.traceField F

/-- The coefficient and sign are fixed here, not existentially fitted.
Every central field and every phase is covered; shell integrability is explicit. -/
structure TranslationWard (F : Spec.Final C o S) : Prop where
  windows {n : ℕ} (x : Points (n+1)) (hx : x ∈ conf (n+1)) :
    ∃ χ : E4 → ℝ, Window x χ
  translation (i : F.α.space.X) {n d : ℕ} {x : Points (n+1)}
    (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag)
    {χ : E4 → ℝ} (hχ : Window x χ) (b : Axis) (B : S.Field d) :
    - ∑ a : Axis, ∫ y : E4,
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q)) =
      Points.gradient 0 b
        (fun z => S.useAt (F.α.ensemble i) z (Fin.cons ⟨d, B⟩ q)) x
  integrable (i : F.α.space.X) {n d : ℕ} {x : Points (n+1)}
    (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag)
    {χ : E4 → ℝ} (hχ : Window x χ) (a b : Axis) (B : S.Field d) :
    Integrable (fun y : E4 =>
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, F.sector.energy a b⟩ (Fin.cons ⟨d, B⟩ q)))
  window_independent (i : F.α.space.X) {n d : ℕ} {x : Points (n+1)}
    (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag)
    {χ ψ : E4 → ℝ} (hχ : Window x χ) (hψ : Window x ψ)
    (b : Axis) (B : S.Field d) :
    shellGrad (F.α.ensemble i) F.sector.energy χ b x q B =
      shellGrad (F.α.ensemble i) F.sector.energy ψ b x q B

/-- The accepted registered local content, no additional null fields and dense
word domain. This is not an isomorphism to a separately specified canonical QFT. -/
structure OperatorContent (F : Spec.Final C o S) : Prop where
  raw_exhaustive (p : Labels.Pol g.core) (hp : p ∈ Labels.invariantSpace g.core) :
    ∃ d : ℕ, ∃ v : Labels.Label g.core d, v.val = p
  free_no_extra_nulls (d : ℕ) : Maxwell.residual g.core d = ⊥
  free_sector (d : ℕ) (p : Maxwell.WickPol g.core) :
    p ∈ Maxwell.shellSector g.core d ↔
      p ∈ Maxwell.Free.lowerCap g.core d ∧
        ∀ u : g.core.El, Maxwell.Free.pigment u p = p
  local_content (d : ℕ) :
    Nonempty (S.Field d ≃ₗ[ℂ] ↥(Maxwell.shellSector g.core d))
  phase_content (i : F.α.space.X) (d : ℕ) :
    Nonempty ((F.α.ensemble i).Field d ≃ₗ[ℂ] ↥(Maxwell.shellSector g.core d))
  dense_words : Dense ((Submodule.span ℂ (Set.range F.action.operators.vector) :
    Submodule ℂ F.action.operators.H) : Set F.action.operators.H)
  faithful (p : S.Union) (hp : p ≠ 0) :
    ∃ f : Boundary.Test4, F.action.operators.field p f ≠ 0

/-- The fixed leading coefficient on the same selected field, in all directions.
No two-loop rate, intrinsic Lambda or positive-order matching is asserted. -/
structure LeadingTrace (F : Spec.Final C o S) : Prop where
  positive : 0 < 3 * (g.core.lieDim : ℝ) / Real.pi ^ 4
  leading : Tendsto (fun x : SpaceTime =>
    YMAFBridge.K₂ F x * ‖x‖ ^ 8 * uvLog 1 x ^ 2)
    (𝓝[≠] 0) (𝓝 (3 * (g.core.lieDim : ℝ) / Real.pi ^ 4))
  group_predicate : KernelUVPowerLaw (YMAFBridge.K₂ F)

/-- Retain the already proved public and stronger source conclusions on F.
These retain their SOURCE status: bundling them is not an independent semantic
verification of every reconstruction, OPE, contact or perturbative definition. -/
def SourceConclusions (hg : g.IsSimple) (F : Spec.Final C o S) : Prop :=
  ∃ (L : EveryPhase.Almanac F)
    (Q : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (M : Contacts.Devices F.sector.derivatives) (X : Climb.Scaling S),
    (YangMills.hierarchy F Q).Properties o.per ∧
    (YangMills.hierarchy F Q).Contacts ∧
    Independent.Core.{0,0} (YangMills.GaugeGroup.coreSimple hg) F L Q ∧
    Nonperturbative.Headline.Reconstruction F L ∧
    (∀ i, (YangMills.view (L.actors i)).Axioms) ∧
    Nonperturbative.Headline.SeparatedOPE F Q ∧
    Nonperturbative.Headline.NestedOPE F Q ∧
    Nonperturbative.Headline.TraceExclusions.{0,0} F ∧
    M.basis = Q.port ∧ Contacts.Solstice.MultipleLight F M ∧
    Nonempty (Contacts.Transport.SystemBasis M) ∧
    Nonempty (Contacts.Solstice.Thresholds M) ∧
    Pert.FirstExtension F X ∧ Pert.Position.FourMeters F X

/-- Proposed combined acceptance at the currently verified scope.
There are no fresh per-clause choices of family, phase or trace. -/
structure Accepted (hg : g.IsSimple) (F : Spec.Final C o S) : Prop where
  lattice : LatticeAndScale C o S
  phase_os : PhaseAndOS F
  translation : TranslationWard F
  operators : OperatorContent F
  trace_uv : LeadingTrace F
  positive_lattice_probe : TwoPointScale.MassLimit F
  source : SourceConclusions hg F

/-- Family precedes the requested order; one refinement and one F serve all
clauses. The input order's UV subsequence is replaced by the full UV order in
the lattice clause, while its IR order is refined as in the submitted result. -/
def CombinedAcceptance (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (b : ℝ) : Prop :=
  ∃ C : Family g.core, C.path.levels.clock.kernel.penalty = b ∧
    ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
      (F : Spec.Final C (p.refine q) S), Accepted hg F

end YMReview.Acceptance
