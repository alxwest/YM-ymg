import ChallengeSpec

/-! Review target for a common OPE within one constructed hierarchy.
The target writes the radius and state quantifiers explicitly. It uses the
public hierarchy's actual fields and correlations, but not its OPE predicate.
Degrees are filtration labels, not asserted exact scaling dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.OPE
open YangMills YangMills.Hierarchy Function Set Filter
open scoped Topology BigOperators Classical
variable {g : GaugeGroup} {C : WilsonFamily g}

def Cluster {n : ℕ} (r M η : ℝ) (x : Fin n → Spacetime) (o : Spacetime) : Prop :=
  (∀ i, ‖x i - o‖ ≤ M * r) ∧
  (∀ i j, i ≠ j → η * r ≤ ‖x i - x j‖)

def Spectators {m : ℕ} (c : ℝ) (y : Fin m → Spacetime) (o : Spacetime) : Prop :=
  (∀ i, c ≤ ‖o - y i‖) ∧
  (∀ i j, i ≠ j → c ≤ ‖y i - y j‖)

def truncated (T : Hierarchy C) {n m : ℕ} (s : Option T.Character)
    (a : Fin n → T.Tag) (x : Fin n → Spacetime)
    (b : Fin m → T.Tag) (y : Fin m → Spacetime) (o : Spacetime) (D : ℕ) : ℂ :=
  ∑ j : Fin (D + 1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
    T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y

/-- Coefficients are already fixed in T, before spectators, truncation,
geometry bounds, radius, or phase are requested. In particular the radius
for the remainder is chosen BEFORE the phase and all admissible positions. -/
structure CommonOPE (T : Hierarchy C) : Prop where
  coefficient_radius {n : ℕ} (a : Fin n → T.Tag) (j : ℕ) (i : T.Channel j)
      (M η ε : ℝ) : 0 ≤ M → 0 < η → 0 < ε →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ∀ x o, Cluster r M η x o →
        ‖T.coefficient a j i x o‖ ≤ r ^ ((j : ℝ) - (∑ k, ((a k).1 : ℝ)) - ε)
  remainder_radius {n m : ℕ} (a : Fin n → T.Tag) (b : Fin m → T.Tag)
      (D : ℕ) (M η c ε : ℝ) : 0 ≤ M → 0 < η → 0 < c → 0 < ε →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ∀ (s : Option T.Character) x o y,
        Cluster r M η x o → Spectators c y o →
          ‖T.grouped s a x b y - truncated T s a x b y o D‖ ≤
            r ^ ((D : ℝ) + 1 - (∑ k, ((a k).1 : ℝ)) - ε)

end YMReview.OPE
