import MixingActionTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.MixingTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre
open YMYMG.DictionaryRenormalization YMYMG.CouplingTaylor
open YMYMG.LegendreTransport YMYMG.ScaleTransport
variable {G : CompactSimpleGaugeGroup}

def delayOne {U : Type*} [Zero U] (c : ℕ → ℕ → U) : ℕ → ℕ → U
  | r+1, l+1 => c r l
  | _, _ => 0

theorem pairedConvolve_delayOne_left {U V : Type*} [Zero U]
    (B : U → V → ℂ) (hB : ∀ v, B 0 v = 0)
    (c : ℕ → ℕ → U) (w : ℕ → ℕ → V) (r l : ℕ) :
    pairedConvolve B (delayOne c) w r l = delayOne (pairedConvolve B c w) r l := by
  cases l with
  | zero => simp [pairedConvolve, delayOne, hB]
  | succ l =>
    cases r with
    | zero => simp [pairedConvolve, delayOne, hB]
    | succ r =>
      change pairedConvolve B (delayOne c) w (r+1) (l+1) = pairedConvolve B c w r l
      unfold pairedConvolve
      conv_lhs => rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, delayOne, hB, Finset.sum_const_zero, zero_add,
        Fin.val_succ, Nat.add_sub_add_right]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, hB, zero_add, Fin.val_succ, Nat.add_sub_add_right]

theorem pairedConvolve_delayOne_right {U V : Type*} [Zero V]
    (B : U → V → ℂ) (hB : ∀ u, B u 0 = 0)
    (c : ℕ → ℕ → U) (w : ℕ → ℕ → V) (r l : ℕ) :
    pairedConvolve B c (delayOne w) r l = delayOne (pairedConvolve B c w) r l := by
  rw [pairedConvolve_swap, pairedConvolve_delayOne_left _ hB]
  exact congrArg (fun f : ℕ → ℕ → ℂ => delayOne f r l)
    (by funext i j; exact pairedConvolve_swap _ w c i j)

def unitRate : ScalarCoefficients := fun r l => if r = 0 ∧ l = 0 then 1 else 0

theorem scalarAction_unit (A : FormalAmplitude G) : scalarAction unitRate A = A := by
  funext r l legs q
  simp [scalarAction, unitRate, Fin.sum_univ_succ]

theorem scalarAction_coefficient_add (c d : ScalarCoefficients) (A : FormalAmplitude G) :
    scalarAction (fun r l => c r l+d r l) A = scalarAction c A + scalarAction d A := by
  funext r l legs q
  simp only [scalarAction, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]

theorem scalarAction_coefficient_scale (a : ℝ) (c : ScalarCoefficients) (A : FormalAmplitude G) :
    scalarAction (fun r l => a*c r l) A = (a : ℂ) • scalarAction c A := by
  funext r l legs q
  simp only [scalarAction, Complex.ofReal_mul, mul_assoc, Finset.mul_sum,
    Pi.smul_apply, smul_eq_mul]

theorem scalarAction_coefficient_delay (c : ScalarCoefficients) (A : FormalAmplitude G) :
    scalarAction (delay c) A = amplitudeDelay (scalarAction c A) := by
  funext r l legs q
  exact pairedConvolve_delay_left (fun (b : ℝ) z => (b : ℂ)*z)
    (fun z => by simp) c (fun i j => A i j legs q) r l

theorem scalarAction_delayOne (c : ScalarCoefficients) (A : FormalAmplitude G) :
    scalarAction (delayOne c) A = scalarAction c (firstDelay A) := by
  funext r l legs q
  calc
    _ = delayOne (fun i j => scalarAction c A i j legs q) r l :=
      pairedConvolve_delayOne_left (fun (b : ℝ) z => (b : ℂ)*z)
        (fun z => by simp) c (fun i j => A i j legs q) r l
    _ = _ := (pairedConvolve_delayOne_right (fun (b : ℝ) z => (b : ℂ)*z)
        (fun b => mul_zero _) c (fun i j => A i j legs q) r l).symm

theorem correctionRate_eq (beta : ScalarCoefficients) (a : ℝ → ℝ) (mu : ℝ) :
    correctionRate beta a mu = fun r l =>
      (mu*deriv a mu)*delay unitRate r l + (2*a mu)*delayOne beta r l := by
  funext r l
  obtain r | r | r := r <;> cases l
  all_goals simp [correctionRate, delay, delayOne, unitRate]

theorem correctionRate_action (beta : ScalarCoefficients) (a : ℝ → ℝ) (mu : ℝ)
    (A : FormalAmplitude G) :
    scalarAction (correctionRate beta a mu) A =
      (mu*deriv a mu : ℝ) • amplitudeDelay A +
      (2*a mu : ℝ) • scalarAction beta (firstDelay A) := by
  rw [correctionRate_eq, scalarAction_coefficient_add, scalarAction_coefficient_scale,
    scalarAction_coefficient_scale, scalarAction_coefficient_delay,
    scalarAction_unit, scalarAction_delayOne]
  rfl

theorem changeMixing_action_expanded (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0) (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (mu : ℝ)
    (J : InvariantInsertionLabel G →ₗ[ℝ] FormalAmplitude G) (p : InvariantInsertionLabel G) :
    mixingAction (changeMixing K D hq beta a ha) mu (dictionaryChange J D (a mu)) p =
      mixingAction K mu J p +
      (a mu * D.weight p : ℝ) • amplitudeDelay (mixingAction K mu J D.lower) -
      (mu * deriv a mu * D.weight p : ℝ) • amplitudeDelay (J D.lower) -
      (2 * a mu * D.weight p : ℝ) • scalarAction beta (firstDelay (J D.lower)) := by
  rw [changeMixing_action, correctionRate_action]
  funext r l legs q
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_mul]
  ring

#print axioms pairedConvolve_delayOne_left
#print axioms pairedConvolve_delayOne_right
#print axioms scalarAction_unit
#print axioms scalarAction_coefficient_add
#print axioms scalarAction_coefficient_scale
#print axioms scalarAction_coefficient_delay
#print axioms scalarAction_delayOne
#print axioms correctionRate_eq
#print axioms correctionRate_action
#print axioms changeMixing_action_expanded
end YMYMG.MixingTransport
