import ScaleDerivativeTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Stability of the native weak composite residual condition. These are
finite linearity and eventual-equality arguments, not new continuum bounds. -/
noncomputable section
open Filter MeasureTheory
namespace YMYMG.ScaleTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.Legendre YangMills.ScaleInsertion
open YMYMG.CouplingTaylor YMYMG.LegendreTransport
variable {G : CompactSimpleGaugeGroup}

theorem weakLocal_zero :
    WeakLocalEndpointZero (fun (_ _ : ℝ) (_ : Spacetime) => (0 : FormalAmplitude G)) := by
  intro r l legs test ht hn
  refine ⟨?_, fun _ => 0, ?_, ?_⟩
  · intro IR hIR
    filter_upwards [eventually_ge_atTop IR] with UV hUV
    refine ⟨hUV, ?_⟩
    change Integrable (fun z => (0 : ℂ) * test z)
    simpa only [zero_mul] using!
      (integrable_zero ((Fin 1 → Spacetime) × (Fin legs.length → Spacetime)) ℂ volume)
  · intro IR hIR
    simpa only [localPairing, localPairingIntegrand, Pi.zero_apply, zero_mul,
      integral_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0))
  · exact tendsto_const_nhds

theorem weakLocal_add {R T : ℝ → ℝ → Spacetime → FormalAmplitude G}
    (hR : WeakLocalEndpointZero R) (hT : WeakLocalEndpointZero T) :
    WeakLocalEndpointZero (fun IR UV x => R IR UV x + T IR UV x) := by
  intro r l legs test ht hn
  obtain ⟨iR, vR, uvR, irR⟩ := hR r l legs test ht hn
  obtain ⟨iT, vT, uvT, irT⟩ := hT r l legs test ht hn
  have he (IR UV : ℝ) :
      localPairingIntegrand (fun IR UV x => R IR UV x + T IR UV x) r l IR UV legs test =
      fun z => localPairingIntegrand R r l IR UV legs test z +
        localPairingIntegrand T r l IR UV legs test z := by
    funext z
    simp only [localPairingIntegrand, Pi.add_apply, add_mul]
  refine ⟨?_, fun IR => vR IR + vT IR, ?_, ?_⟩
  · intro IR hIR
    filter_upwards [iR IR hIR, iT IR hIR] with UV hr hh
    refine ⟨hr.1, ?_⟩
    rw [he]
    exact hr.2.add hh.2
  · intro IR hIR
    apply ((uvR IR hIR).add (uvT IR hIR)).congr'
    filter_upwards [iR IR hIR, iT IR hIR] with UV hr hh
    simp only [localPairing, he]
    exact (integral_add hr.2 hh.2).symm
  · simpa only [add_zero] using irR.add irT

theorem weakLocal_smul (c : ℂ) {R : ℝ → ℝ → Spacetime → FormalAmplitude G}
    (hR : WeakLocalEndpointZero R) :
    WeakLocalEndpointZero (fun IR UV x => c • R IR UV x) := by
  intro r l legs test ht hn
  obtain ⟨iR, vR, uvR, irR⟩ := hR r l legs test ht hn
  have he (IR UV : ℝ) :
      localPairingIntegrand (fun IR UV x => c • R IR UV x) r l IR UV legs test =
      fun z => c * localPairingIntegrand R r l IR UV legs test z := by
    funext z
    simp only [localPairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
  refine ⟨?_, fun IR => c * vR IR, ?_, ?_⟩
  · intro IR hIR
    filter_upwards [iR IR hIR] with UV hr
    refine ⟨hr.1, ?_⟩
    rw [he]
    exact hr.2.const_mul c
  · intro IR hIR
    simpa only [localPairing, he, integral_const_mul] using
      (uvR IR hIR).const_mul c
  · simpa only [mul_zero] using irR.const_mul c

theorem weakLocal_delay {R : ℝ → ℝ → Spacetime → FormalAmplitude G}
    (hR : WeakLocalEndpointZero R) :
    WeakLocalEndpointZero (fun IR UV x => amplitudeDelay (R IR UV x)) := by
  intro r l legs test ht hn
  obtain r | r | r := r
  · simpa only [localPairing, localPairingIntegrand, amplitudeDelay, delay, Pi.zero_apply] using!
      (weakLocal_zero (G := G) 0 0 legs test ht hn)
  · simpa only [localPairing, localPairingIntegrand, amplitudeDelay, delay, Pi.zero_apply] using!
      (weakLocal_zero (G := G) 0 0 legs test ht hn)
  · cases l with
    | zero =>
      simpa only [localPairing, localPairingIntegrand, amplitudeDelay, delay, Pi.zero_apply] using!
        (weakLocal_zero (G := G) 0 0 legs test ht hn)
    | succ l =>
      simpa only [localPairing, localPairingIntegrand, amplitudeDelay, delay] using!
        (hR r l legs test ht hn)

/-- Only eventual UV equality at each positive IR is needed. In particular,
identities valid for UV above the subtraction scale suffice for this step. -/
theorem weakLocal_congr_eventually {R T : ℝ → ℝ → Spacetime → FormalAmplitude G}
    (hR : WeakLocalEndpointZero R)
    (he : ∀ IR, 0 < IR → ∀ᶠ UV in atTop, R IR UV = T IR UV) :
    WeakLocalEndpointZero T := by
  intro r l legs test ht hn
  obtain ⟨iR, vR, uvR, irR⟩ := hR r l legs test ht hn
  have hi (IR UV : ℝ) (hh : R IR UV = T IR UV) :
      localPairingIntegrand R r l IR UV legs test =
        localPairingIntegrand T r l IR UV legs test := by
    funext z
    simp only [localPairingIntegrand, hh]
  refine ⟨?_, vR, ?_, irR⟩
  · intro IR hIR
    filter_upwards [iR IR hIR, he IR hIR] with UV hr hh
    exact ⟨hr.1, (hi IR UV hh) ▸ hr.2⟩
  · intro IR hIR
    apply (uvR IR hIR).congr'
    filter_upwards [he IR hIR] with UV hh
    exact congrArg (fun f => ∫ z, f z) (hi IR UV hh)

#print axioms weakLocal_zero
#print axioms weakLocal_add
#print axioms weakLocal_smul
#print axioms weakLocal_delay
#print axioms weakLocal_congr_eventually
end YMYMG.ScaleTransport
