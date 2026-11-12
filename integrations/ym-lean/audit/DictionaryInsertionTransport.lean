import DictionaryRenormalization
import CouplingTaylorShift

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace YMYMG.DictionaryRenormalization
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor
variable {G : CompactSimpleGaugeGroup} {lift : QuantumObservableLift G}

def insertionFunctional (L : InsertedFlowFamily G) (x : Spacetime)
    (loop : ℕ) (IR UV : ℝ) (legs : List (ExternalLeg G))
    (momenta : Fin legs.length → Spacetime) : (LocalMonomial G →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun m => L [⟨m,x⟩] loop IR UV legs momenta)

theorem insertionFunctional_apply (L : InsertedFlowFamily G) (x : Spacetime)
    (loop : ℕ) (IR UV : ℝ) (legs : List (ExternalLeg G))
    (momenta : Fin legs.length → Spacetime) (c : LocalMonomial G →₀ ℂ) :
    insertionFunctional L x loop IR UV legs momenta c =
      c.sum (fun m a => a * L [⟨m,x⟩] loop IR UV legs momenta) := by
  simp [insertionFunctional, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

theorem finiteInsertion_zero (D : Direction G) (a g : ℝ) (L : InsertedFlowFamily G)
    (p : InvariantInsertionLabel G) (x : Spacetime) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (momenta : Fin legs.length → Spacetime) :
    (change lift D a).finiteInsertion L g p x 0 IR UV legs momenta =
      lift.finiteInsertion L g p x 0 IR UV legs momenta := by
  simp [QuantumObservableLift.finiteInsertion, change]

theorem finiteInsertion_succ (D : Direction G) (a g : ℝ) (L : InsertedFlowFamily G)
    (p : InvariantInsertionLabel G) (x : Spacetime) (loop : ℕ) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (momenta : Fin legs.length → Spacetime) :
    (change lift D a).finiteInsertion L g p x (loop+1) IR UV legs momenta =
      lift.finiteInsertion L g p x (loop+1) IR UV legs momenta +
        ((g : ℂ)^2 * (a * D.weight p : ℝ)) *
          lift.finiteInsertion L g D.lower x loop IR UV legs momenta := by
  simp only [QuantumObservableLift.finiteInsertion, ← insertionFunctional_apply]
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => lhs; rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right,
    change, map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

variable {B : InvariantForm G} {e : ColorFrame B}
  {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}

def physicalJets (lift : QuantumObservableLift G) (p : InvariantInsertionLabel G)
    (m : LocalMonomial G) (order loop : ℕ) : ℂ :=
  jet order (fun g => lift.physicalCoefficient g p loop m)

theorem physicalJets_change (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ)
    (p : InvariantInsertionLabel G) (m : LocalMonomial G) :
    physicalJets (change lift D a) p m = fun order loop => physicalJets lift p m order loop +
      (a * D.weight p : ℝ) * delay (physicalJets lift D.lower m) order loop := by
  funext order loop
  cases loop with
  | zero => simp [physicalJets, change, QuantumShift.shifted, delay]
  | succ loop =>
    have hs : ContDiff ℝ ∞ (fun g : ℝ => (g : ℂ)^2 * (a * D.weight p : ℝ) *
        lift.physicalCoefficient g D.lower loop m) :=
      ((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul
        (h.physical_coupling_smooth D.lower loop m)
    simp only [physicalJets, change, QuantumShift.shifted, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    rw [jet_add _ _ _ (h.physical_coupling_smooth p (loop+1) m) hs]
    have he : (fun g : ℝ => (g : ℂ)^2 * (a * D.weight p : ℝ) *
        lift.physicalCoefficient g D.lower loop m) =
        fun g : ℝ => (a * D.weight p : ℝ) * ((g : ℂ)^2 *
          lift.physicalCoefficient g D.lower loop m) := by funext g; ring
    rw [he, jet_const_mul, jet_mul_square _ _ (h.physical_coupling_smooth D.lower loop m)]
    obtain order | order | order := order
    all_goals simp [delay, physicalJets]

theorem physicalJets_outside (h : lift.Compatible e anomaly Q)
    (p : InvariantInsertionLabel G) (m : LocalMonomial G)
    (hm : intrinsicEngineeringDimension p < m.dimension) (order loop : ℕ) :
    physicalJets lift p m order loop = 0 := by
  have he : (fun g => lift.physicalCoefficient g p loop m) = 0 := by
    funext g
    by_contra hn
    exact (not_le_of_gt hm) (h.physical_support g p loop m hn).2.1
  simp [physicalJets, he, jet]

def continuumValue (lift : QuantumObservableLift G)
    (W : LocalMonomial G → ℕ → ℕ → ℂ) (p : InvariantInsertionLabel G)
    (order loop : ℕ) : ℂ :=
  ∑ m ∈ monomialsBelow G (intrinsicEngineeringDimension p+1),
    convolve (physicalJets lift p m) (W m) order loop

theorem continuumValue_bound (h : lift.Compatible e anomaly Q)
    (W : LocalMonomial G → ℕ → ℕ → ℂ) (p : InvariantInsertionLabel G)
    (bound : ℕ) (hb : intrinsicEngineeringDimension p ≤ bound) (order loop : ℕ) :
    (∑ m ∈ monomialsBelow G (bound+1),
      convolve (physicalJets lift p m) (W m) order loop) =
        continuumValue lift W p order loop := by
  classical
  symm
  apply Finset.sum_subset
  · intro m hm
    have hs := (mem_monomialsBelow_iff _ m).mp hm
    exact (mem_monomialsBelow_iff _ m).mpr ⟨hs.1, by omega⟩
  · intro m hm hn
    have hs := (mem_monomialsBelow_iff _ m).mp hm
    have hd : intrinsicEngineeringDimension p < m.dimension := by
      by_contra hh
      apply hn
      exact (mem_monomialsBelow_iff _ m).mpr ⟨hs.1, by omega⟩
    simp [convolve, physicalJets_outside h p m hd]

theorem continuumValue_change (h : lift.Compatible e anomaly Q) (D : Direction G)
    (a : ℝ) (W : LocalMonomial G → ℕ → ℕ → ℂ) (p : InvariantInsertionLabel G)
    (order loop : ℕ) :
    continuumValue (change lift D a) W p order loop = continuumValue lift W p order loop +
      (a * D.weight p : ℝ) * delay (continuumValue lift W D.lower) order loop := by
  classical
  simp only [continuumValue, physicalJets_change h, convolve_add, convolve_const_mul,
    convolve_delay, Finset.sum_add_distrib, ← Finset.mul_sum]
  by_cases hw : D.weight p = 0
  · simp [hw]
  · apply congrArg (fun z : ℂ => continuumValue lift W p order loop +
      (a * D.weight p : ℝ) * z)
    cases loop with
    | zero => simp [delay]
    | succ loop =>
      obtain order | order | order := order
      · simp [delay]
      · simp [delay]
      · simp only [delay]
        exact continuumValue_bound h W D.lower _ (D.filtered p hw) order loop

theorem physicalInsertion_value (W : WardContinuumData G) (p : InvariantInsertionLabel G)
    (order loop : ℕ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    lift.physicalInsertion W p order loop legs test =
      continuumValue lift (fun m i j => W.physical .single i j (fun _ => m) legs test)
        p order loop := by
  simp only [QuantumObservableLift.physicalInsertion, continuumValue, convolve, physicalJets,
    jet, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem ultravioletInsertion_value (W : WardContinuumData G) (p : InvariantInsertionLabel G)
    (order loop : ℕ) (IR : ℝ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    lift.ultravioletInsertion W p order loop IR legs test =
      continuumValue lift (fun m i j => W.ultraviolet .single i j IR (fun _ => m) legs test)
        p order loop := by
  simp only [QuantumObservableLift.ultravioletInsertion, continuumValue, convolve, physicalJets,
    jet, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem physicalInsertion_change (h : lift.Compatible e anomaly Q) (D : Direction G)
    (a : ℝ) (W : WardContinuumData G) (p : InvariantInsertionLabel G) (order loop : ℕ)
    (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    (change lift D a).physicalInsertion W p order loop legs test =
      lift.physicalInsertion W p order loop legs test + (a * D.weight p : ℝ) *
        delay (fun i j => lift.physicalInsertion W D.lower i j legs test) order loop := by
  simpa only [physicalInsertion_value] using continuumValue_change h D a
    (fun m i j => W.physical .single i j (fun _ => m) legs test) p order loop

theorem ultravioletInsertion_change (h : lift.Compatible e anomaly Q) (D : Direction G)
    (a : ℝ) (W : WardContinuumData G) (p : InvariantInsertionLabel G) (order loop : ℕ)
    (IR : ℝ) (legs : List (ExternalLeg G)) (test : JointMomentumTest 1 legs) :
    (change lift D a).ultravioletInsertion W p order loop IR legs test =
      lift.ultravioletInsertion W p order loop IR legs test + (a * D.weight p : ℝ) *
        delay (fun i j => lift.ultravioletInsertion W D.lower i j IR legs test) order loop := by
  simpa only [ultravioletInsertion_value] using continuumValue_change h D a
    (fun m i j => W.ultraviolet .single i j IR (fun _ => m) legs test) p order loop

def finiteValue (lift : QuantumObservableLift G) (L : ℝ → InsertedFlowFamily G)
    (p : InvariantInsertionLabel G) (x : Spacetime) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (momenta : Fin legs.length → Spacetime)
    (order loop : ℕ) : ℂ :=
  jet order (fun g => lift.finiteInsertion (L g) g p x loop IR UV legs momenta)

variable {L : ℝ → InsertedFlowFamily G} {W : WardContinuumData G}

theorem finiteValue_change (hl : lift.LimitCompatible L W) (D : Direction G) (a : ℝ)
    (p : InvariantInsertionLabel G) (x : Spacetime) (IR UV : ℝ)
    (hIR : 0 < IR) (hUV : IR ≤ UV) (legs : List (ExternalLeg G))
    (momenta : Fin legs.length → Spacetime) (order loop : ℕ) :
    finiteValue (change lift D a) L p x IR UV legs momenta order loop =
      finiteValue lift L p x IR UV legs momenta order loop + (a * D.weight p : ℝ) *
        delay (finiteValue lift L D.lower x IR UV legs momenta) order loop := by
  have hpair : ContDiff ℝ ∞ (fun g : ℝ => (g, momenta)) :=
    contDiff_id.prodMk contDiff_const
  have hc (p : InvariantInsertionLabel G) (loop : ℕ) : ContDiff ℝ ∞
      (fun g => lift.finiteInsertion (L g) g p x loop IR UV legs momenta) := by
    simpa only [Function.comp_def] using!
      (hl.coupling_momentum_smooth p x loop IR UV hIR hUV legs).comp hpair
  cases loop with
  | zero => simp [finiteValue, finiteInsertion_zero, delay]
  | succ loop =>
    simp only [finiteValue, finiteInsertion_succ]
    have hs : ContDiff ℝ ∞ (fun g : ℝ => (g : ℂ)^2 * (a * D.weight p : ℝ) *
        lift.finiteInsertion (L g) g D.lower x loop IR UV legs momenta) :=
      ((Complex.ofRealCLM.contDiff.pow 2).mul contDiff_const).mul (hc D.lower loop)
    rw [jet_add _ _ _ (hc p (loop+1)) hs]
    have he : (fun g : ℝ => (g : ℂ)^2 * (a * D.weight p : ℝ) *
        lift.finiteInsertion (L g) g D.lower x loop IR UV legs momenta) =
        fun g : ℝ => (a * D.weight p : ℝ) * ((g : ℂ)^2 *
          lift.finiteInsertion (L g) g D.lower x loop IR UV legs momenta) := by funext g; ring
    rw [he, jet_const_mul, jet_mul_square _ _ (hc D.lower loop)]
    obtain order | order | order := order
    all_goals simp [delay, finiteValue]

theorem finiteIntegrand_change (hl : lift.LimitCompatible L W) (D : Direction G) (a : ℝ)
    (p : InvariantInsertionLabel G) (order loop : ℕ) (IR UV : ℝ)
    (hIR : 0 < IR) (hUV : IR ≤ UV) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs)
    (xq : (Fin 1 → Spacetime) × (Fin legs.length → Spacetime)) :
    (change lift D a).finiteIntegrand L p order loop IR UV legs test xq =
      lift.finiteIntegrand L p order loop IR UV legs test xq + (a * D.weight p : ℝ) *
        delay (fun i j => lift.finiteIntegrand L D.lower i j IR UV legs test xq) order loop := by
  change finiteValue (change lift D a) L p (xq.1 0) IR UV legs xq.2 order loop * test xq =
    finiteValue lift L p (xq.1 0) IR UV legs xq.2 order loop * test xq + _
  rw [finiteValue_change hl D a p (xq.1 0) IR UV hIR hUV]
  have he := map_delay (fun z : ℂ => z * test xq) (by simp)
    (finiteValue lift L D.lower (xq.1 0) IR UV legs xq.2) order loop
  change delay (finiteValue lift L D.lower (xq.1 0) IR UV legs xq.2) order loop * test xq =
    delay (fun i j => lift.finiteIntegrand L D.lower i j IR UV legs test xq) order loop at he
  rw [← he]
  ring

theorem delayed_integrable (hl : lift.LimitCompatible L W)
    (p : InvariantInsertionLabel G) (order loop : ℕ) (IR UV : ℝ)
    (hIR : 0 < IR) (hUV : IR ≤ UV) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs) (ht : HasCompactSupport test) :
    Integrable (fun xq =>
      delay (fun i j => lift.finiteIntegrand L p i j IR UV legs test xq) order loop) := by
  obtain order | order | order := order <;> cases loop
  all_goals first
    | exact hl.finite_integrable p _ _ IR UV legs test hIR hUV ht
    | exact integrable_zero _ _ _

theorem finiteIntegral_change (hl : lift.LimitCompatible L W) (D : Direction G) (a : ℝ)
    (p : InvariantInsertionLabel G) (order loop : ℕ) (IR UV : ℝ)
    (hIR : 0 < IR) (hUV : IR ≤ UV) (legs : List (ExternalLeg G))
    (test : JointMomentumTest 1 legs) (ht : HasCompactSupport test) :
    (∫ xq, (change lift D a).finiteIntegrand L p order loop IR UV legs test xq) =
      (∫ xq, lift.finiteIntegrand L p order loop IR UV legs test xq) +
        (a * D.weight p : ℝ) * delay
          (fun i j => ∫ xq, lift.finiteIntegrand L D.lower i j IR UV legs test xq) order loop := by
  simp_rw [finiteIntegrand_change hl D a p order loop IR UV hIR hUV]
  rw [integral_add (hl.finite_integrable p order loop IR UV legs test hIR hUV ht)
    ((delayed_integrable hl D.lower order loop IR UV hIR hUV legs test ht).const_mul _),
    integral_const_mul]
  apply congrArg (fun z : ℂ => (∫ xq, lift.finiteIntegrand L p order loop IR UV legs test xq) +
    (a * D.weight p : ℝ) * z)
  obtain order | order | order := order <;> cases loop <;> simp [delay]

/-- The complete native weak insertion-limit bundle is preserved, including
the real-coupling derivatives, compact-test integrability, and UV-then-IR
order of limits. No new limit-interchange hypothesis is introduced. -/
theorem limitCompatible (h : lift.Compatible e anomaly Q) (hl : lift.LimitCompatible L W)
    (D : Direction G) (a : ℝ) : (change lift D a).LimitCompatible L W where
  coupling_momentum_smooth p x loop IR UV hIR hUV legs := by
    cases loop with
    | zero => simpa only [finiteInsertion_zero] using
        hl.coupling_momentum_smooth p x 0 IR UV hIR hUV legs
    | succ loop =>
      simp only [finiteInsertion_succ]
      have hp := hl.coupling_momentum_smooth p x (loop+1) IR UV hIR hUV legs
      have hq := hl.coupling_momentum_smooth D.lower x loop IR UV hIR hUV legs
      exact hp.add (((((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow 2).mul
        contDiff_const)).mul hq)
  finite_integrable p order loop IR UV legs test hIR hUV ht := by
    change Integrable (fun xq => (change lift D a).finiteIntegrand L p order loop IR UV legs test xq)
    simp_rw [finiteIntegrand_change hl D a p order loop IR UV hIR hUV]
    exact (hl.finite_integrable p order loop IR UV legs test hIR hUV ht).add
      ((delayed_integrable hl D.lower order loop IR UV hIR hUV legs test ht).const_mul _)
  ultraviolet_limit p order loop IR legs test hIR ht := by
    rw [ultravioletInsertion_change h D a]
    have hp := hl.ultraviolet_limit p order loop IR legs test hIR ht
    have hq := delay_tendsto
      (fun UV i j => ∫ xq, lift.finiteIntegrand L D.lower i j IR UV legs test xq)
      (fun i j => lift.ultravioletInsertion W D.lower i j IR legs test)
      (fun i j => hl.ultraviolet_limit D.lower i j IR legs test hIR ht) order loop
    apply (hp.add (hq.const_mul ((a * D.weight p : ℝ) : ℂ))).congr'
    filter_upwards [eventually_ge_atTop IR] with UV hUV
    exact (finiteIntegral_change hl D a p order loop IR UV hIR hUV legs test ht).symm
  infrared_limit p order loop legs test ht hn := by
    simp_rw [ultravioletInsertion_change h D a, physicalInsertion_change h D a]
    have hp := hl.infrared_limit p order loop legs test ht hn
    have hq := delay_tendsto
      (fun IR i j => lift.ultravioletInsertion W D.lower i j IR legs test)
      (fun i j => lift.physicalInsertion W D.lower i j legs test)
      (fun i j => hl.infrared_limit D.lower i j legs test ht hn) order loop
    exact hp.add (hq.const_mul _)

/-- The same bulk, connected hierarchy, action, quantum differential and
all contact Ward identities work with the changed dictionary. -/
theorem fullWardRestoration
    {F : ℝ → OversubtractedFamily G} {C : ConnectedWardData G}
    {T : SameTheoryWardTransportData e L} {pair : ℝ → ContactAnomalyCoefficients G}
    {Q2 : ℝ → ContactAnomalyLimit G}
    (h : FullMultiWardRestoration e L F W C T pair Q Q2 lift)
    (D : Direction G) (a : ℝ) :
    FullMultiWardRestoration e L F W C T pair Q Q2 (change lift D a) where
  same_bulk := h.same_bulk
  same_connected := h.same_connected
  same_contact := h.same_contact
  same_dictionary := compatible h.same_dictionary D a
  same_dictionary_limit := limitCompatible h.same_dictionary h.same_dictionary_limit D a
  action := h.action
  single := h.single
  nilpotent := h.nilpotent
  multiple := h.multiple

/-- For the elementary directions constructed from a strictly higher basis
coordinate, the complete restoration proposition is logically equivalent
before and after the finite renormalization. -/
theorem fullWardRestoration_iff
    {F : ℝ → OversubtractedFamily G} {C : ConnectedWardData G}
    {T : SameTheoryWardTransportData e L} {pair : ℝ → ContactAnomalyCoefficients G}
    {Q2 : ℝ → ContactAnomalyLimit G}
    (D : Direction G) (a : ℝ) (hq : D.weight D.lower = 0) :
    FullMultiWardRestoration e L F W C T pair Q Q2 (change lift D a) ↔
      FullMultiWardRestoration e L F W C T pair Q Q2 lift := by
  constructor
  · intro h
    have hb := fullWardRestoration h D (-a)
    simpa only [change_inverse D a hq] using hb
  · intro h
    exact fullWardRestoration h D a

#print axioms fullWardRestoration
#print axioms fullWardRestoration_iff
#print axioms limitCompatible
#print axioms physicalInsertion_value
#print axioms ultravioletInsertion_value
#print axioms physicalInsertion_change
#print axioms ultravioletInsertion_change
#print axioms finiteValue_change
#print axioms finiteIntegrand_change
#print axioms delayed_integrable
#print axioms finiteIntegral_change
#print axioms physicalJets_change
#print axioms physicalJets_outside
#print axioms continuumValue_bound
#print axioms continuumValue_change

#print axioms insertionFunctional_apply
#print axioms finiteInsertion_zero
#print axioms finiteInsertion_succ
end YMYMG.DictionaryRenormalization
