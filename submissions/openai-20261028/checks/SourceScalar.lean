import YM.Trace.Center

/-! The centered stress trace in the selected phase of the given Final witness.
No state, subtraction, or extraction is chosen by this adapter. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM YM.Table MeasureTheory
open scoped Topology ContDiff

variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

def scalarKernel (n : ℕ) (x : Points n) : ℂ :=
  S.useAt (Trace.state F) x (fun _ => ⟨4, Trace.traceField F⟩)

theorem scalarKernel_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (scalarKernel F n) (conf n) :=
  S.class_smooth _ (F.phase.phase.states F.α.atPoint).smooth _

theorem scalarKernel_translation {n : ℕ} (x : Points n) (hx : x ∈ conf n) (a : E4) :
    scalarKernel F n (Points.across a x) = scalarKernel F n x :=
  (F.phase.phase.states F.α.atPoint).translations n x hx a
    (fun _ => ⟨4, S.representative 4 (Trace.traceField F)⟩)

theorem scalarKernel_permutation {n : ℕ} (x : Points n) (hx : x ∈ conf n)
    (σ : Equiv.Perm (Fin n)) :
    scalarKernel F n (Points.rearrange σ x) = scalarKernel F n x :=
  S.class_perm _ (F.phase.phase.states F.α.atPoint).laws.toSymmetric σ hx
    (fun _ => ⟨4, Trace.traceField F⟩)

theorem scalarKernel_rotation {n : ℕ} (x : Points n) (hx : x ∈ conf n) (R : Ortho) :
    scalarKernel F n (Points.move R x) = scalarKernel F n x := by
  have h := F.phase.phase.sym F.α.atPoint n
    (fun _ => (⟨4, Trace.traceField F⟩ : S.Tag)) x hx R
  simpa only [scalarKernel, Trace.state, Rotation.label, Function.comp_def,
    Trace.traceField, Trace.theta_fixed]
    using h

theorem scalarKernel_real {n : ℕ} (x : Points n) (hx : x ∈ conf n) :
    star (scalarKernel F n x) = scalarKernel F n x := by
  let v := S.representative 4 (Trace.traceField F)
  have hv : S.project 4 v = Trace.traceField F := S.rep _ _
  have hbar : S.project 4 (star v) = S.project 4 v := by
    rw [← S.conj_project F.room.kernel.spin, hv]
    exact Trace.theta_real F _
  have h := (F.phase.phase.states F.α.atPoint).spin.real hx
    (fun _ : Fin n => (⟨4, v⟩ : C.book.Token))
  change (Trace.state F).value (fun _ => 4) x (fun _ => star v) =
    star (scalarKernel F n x) at h
  rw [← h]
  exact S.agrees (Trace.state F) (F.phase.phase.states F.α.atPoint).laws.toSymmetric
    (Trace.fits F) hx (fun _ => hbar)

theorem scalarKernel_zero (x : Points 0) : scalarKernel F 0 x = 1 :=
  (F.phase.phase.states F.α.atPoint).laws.trivial
    (fun _ => ⟨4, S.representative 4 (Trace.traceField F)⟩) x

theorem scalarKernel_one (x : Points 1) : scalarKernel F 1 x = 0 :=
  Trace.centered_zero F x

/-- Finite singular order for each fixed arity and derivative order. This is
not the OS-II bound with one order growing linearly in arity. -/
theorem scalarKernel_capped (n j : ℕ) :
    ∃ A : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x →
        ‖iteratedFDeriv ℝ j (scalarKernel F n) x‖ ≤ B * r⁻¹ ^ A :=
  (F.phase.phase.states F.α.atPoint).order n (fun _ => 4)
    (fun _ => S.representative 4 (Trace.traceField F)) j

#print axioms scalarKernel_rotation
#print axioms scalarKernel_real
#print axioms scalarKernel_capped
end YMOSBridge
