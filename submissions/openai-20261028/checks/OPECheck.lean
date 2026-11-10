import OPESpec
import Solution

set_option autoImplicit false
noncomputable section
namespace YMReview.OPE
open YangMills YangMills.Hierarchy Function Set Filter
open scoped Topology BigOperators Classical
variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

private theorem radius_of_eventually {P : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r, 0 < r → r < ρ → P r := by
  obtain ⟨ρ, hρ, hP⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h
  exact ⟨ρ, hρ, fun r hr hrρ => hP ⟨hr, hrρ⟩⟩

/-- Translate the source OPE into the review's explicit radius statement. -/
theorem from_source (h : T.OperatorProductExpansion) : CommonOPE T := by
  constructor
  · intro n a j i M η ε hM hη hε
    obtain ⟨ρ, hρ, hr⟩ := radius_of_eventually (h.coefficients a M η ε hM hη hε j i)
    exact ⟨ρ, hρ, fun r hpos hsmall x o hx => hr r hpos hsmall x o hx⟩
  · intro n m a b D M η c ε hM hη hc hε
    obtain ⟨ρ, hρ, hr⟩ := radius_of_eventually (h.remainder a b M η c ε hM hη hc hε D)
    exact ⟨ρ, hρ, fun r hpos hsmall s x o y hx hy => hr r hpos hsmall x o y hx hy s⟩

/-- Subtracting two phases preserves exactly the same OPE coefficients.
The estimate is uniform in BOTH phases, with twice the original remainder. -/
theorem phase_difference (h : CommonOPE T) {n m : ℕ}
    (a : Fin n → T.Tag) (b : Fin m → T.Tag) (D : ℕ) (M η c ε : ℝ)
    (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ∀ (s t : Option T.Character) x o y,
        Cluster r M η x o → Spectators c y o →
          ‖(T.grouped s a x b y - T.grouped t a x b y) -
            ∑ j : Fin (D + 1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
              (T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y -
               T.grouped t (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y)‖
          ≤ 2 * r ^ ((D : ℝ) + 1 - (∑ k, ((a k).1 : ℝ)) - ε) := by
  obtain ⟨ρ, hρ, hr⟩ := h.remainder_radius a b D M η c ε hM hη hc hε
  refine ⟨ρ, hρ, fun r hpos hsmall s t x o y hx hy => ?_⟩
  have hs := hr r hpos hsmall s x o y hx hy
  have ht := hr r hpos hsmall t x o y hx hy
  have he : (T.grouped s a x b y - T.grouped t a x b y) -
      ∑ j : Fin (D + 1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
        (T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y -
         T.grouped t (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y) =
      (T.grouped s a x b y - truncated T s a x b y o D) -
      (T.grouped t a x b y - truncated T t a x b y o D) := by
    simp only [truncated, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hs ht).trans_eq (by ring))

/-- One family is chosen before every requested volume sequence. The review
check and original Properties hold for the SAME resulting hierarchy. -/
theorem constructed (g : GaugeGroup) (hg : g.IsSimple) :
    ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ CommonOPE T := by
  obtain ⟨C, hC, orders⟩ := YangMills.jointExistence g hg
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT⟩ := orders p hp
  exact ⟨q, hq, T, hT, from_source hT.ope⟩

section FieldDictionary
open YM YM.Table YM.OPE.Orbits
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
    (F : Spec.Final C o S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- Channels assemble into the actual degree-j coefficient field. -/
theorem channel_assembly {I : Type} [Fintype I] {d : I → ℕ}
    (a : Labels S d) (x : I → E4) (z : E4) (j : ℕ) :
    ∑ i : Q.channels j, Q.coef j i x a z • Q.actor j i = Q.fresh j x z a :=
  Q.assemble j x a z

/-- A single insertion is recovered exactly once its degree is included. -/
theorem single_field (D j : ℕ) (hj : j ≤ D) (a : S.Field j) :
    Q.packet D (YM.OPE.sole 0) (YM.OPE.sole a : Labels S (fun _ : Unit => j)) 0 =
      F.sector.derivatives.rise hj a :=
  Q.packet_single D j hj a
end FieldDictionary
end YMReview.OPE

#print axioms YMReview.OPE.from_source
#print axioms YMReview.OPE.phase_difference
#print axioms YMReview.OPE.constructed
#print axioms YMReview.OPE.channel_assembly
#print axioms YMReview.OPE.single_field
