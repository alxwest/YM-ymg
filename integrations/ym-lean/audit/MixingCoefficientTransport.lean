import FilteredLabelShear

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Native finite mixing data for an elementary dictionary correction.
The graph guards and every CompositeMixing field are retained. The separate
residual identity is needed before these data give a scale normalization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.MixingTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion
open YMYMG.DictionaryRenormalization YMYMG.CouplingTaylor
variable {G : CompactSimpleGaugeGroup}

def addMixing (K H : CompositeMixing G) : CompositeMixing G where
  coefficient mu r l p := K.coefficient mu r l p + H.coefficient mu r l p
  filtered mu r l p q h := by
    by_cases hk : K.coefficient mu r l p q = 0
    · apply H.filtered mu r l p q
      simpa only [Finsupp.add_apply, hk, zero_add] using h
    · exact K.filtered mu r l p q hk
  smooth r l p q := (K.smooth r l p q).add (H.smooth r l p q)
  classical mu r p hmu := by rw [K.classical mu r p hmu, H.classical mu r p hmu, add_zero]
  unit mu r l hmu := by rw [K.unit mu r l hmu, H.unit mu r l hmu, add_zero]
  linear_add mu r l p q := by rw [K.linear_add, H.linear_add]; abel
  linear_smul mu r l c p := by rw [K.linear_smul, H.linear_smul, smul_add]

def scaleMixing (K : CompositeMixing G) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) : CompositeMixing G where
  coefficient mu r l p := a mu • K.coefficient mu r l p
  filtered mu r l p q h := by
    apply K.filtered mu r l p q
    intro hz
    apply h
    simp [Finsupp.smul_apply, hz]
  smooth r l p q := ha.mul (K.smooth r l p q)
  classical mu r p hmu := by rw [K.classical mu r p hmu, smul_zero]
  unit mu r l hmu := by rw [K.unit mu r l hmu, smul_zero]
  linear_add mu r l p q := by rw [K.linear_add, smul_add]
  linear_smul mu r l c p := by rw [K.linear_smul, smul_comm]

def subMixing (K H : CompositeMixing G) : CompositeMixing G :=
  addMixing K (scaleMixing H (fun _ => -1) contDiffOn_const)

theorem subMixing_coefficient (K H : CompositeMixing G) (mu : ℝ) (r l : ℕ)
    (p : InvariantInsertionLabel G) :
    (subMixing K H).coefficient mu r l p =
      K.coefficient mu r l p - H.coefficient mu r l p := by
  simp [subMixing, addMixing, scaleMixing, sub_eq_add_neg]

def delayMixing (K : CompositeMixing G) : CompositeMixing G where
  coefficient mu r l p := delay (fun i j => K.coefficient mu i j p) r l
  filtered mu r l p q h := by
    obtain r | r | r := r <;> cases l
    all_goals first | exact (h rfl).elim | exact K.filtered _ _ _ _ _ h
  smooth r l p q := by
    obtain r | r | r := r <;> cases l
    all_goals first | exact contDiffOn_const | exact K.smooth _ _ _ _
  classical mu r p _ := by obtain r | r | r := r <;> rfl
  unit mu r l hmu := by
    obtain r | r | r := r <;> cases l
    all_goals first | rfl | exact K.unit _ _ _ hmu
  linear_add mu r l p q := by
    obtain r | r | r := r <;> cases l
    all_goals first | exact (zero_add 0).symm | exact K.linear_add _ _ _ _ _
  linear_smul mu r l c p := by
    obtain r | r | r := r <;> cases l
    all_goals first | exact (smul_zero _).symm | exact K.linear_smul _ _ _ _ _

def inputMixing (K : CompositeMixing G) (D : Direction G) : CompositeMixing G where
  coefficient mu r l p := D.weight p • K.coefficient mu r l D.lower
  filtered mu r l p q h := by
    have hp : D.weight p ≠ 0 := by
      intro hz; apply h; simp [hz]
    have hk : K.coefficient mu r l D.lower q ≠ 0 := by
      intro hz; apply h; simp [Finsupp.smul_apply, hz]
    exact (K.filtered _ _ _ _ _ hk).trans (D.filtered p hp)
  smooth r l p q := contDiffOn_const.mul (K.smooth r l D.lower q)
  classical mu r p hmu := by rw [K.classical mu r D.lower hmu, smul_zero]
  unit mu r l _ := by rw [D.unit, zero_smul]
  linear_add mu r l p q := by rw [map_add, add_smul]
  linear_smul mu r l c p := by simp only [map_smul, smul_eq_mul, smul_smul]

def rankMixing (D : Direction G) (f : ℝ → ℕ → ℕ → ℝ)
    (hf : ∀ r l, ContDiffOn ℝ ∞ (fun mu => f mu r l) (Set.Ioi 0))
    (hf0 : ∀ mu r, 0 < mu → f mu r 0 = 0) : CompositeMixing G where
  coefficient mu r l p := Finsupp.single D.lower (f mu r l * D.weight p)
  filtered mu r l p q h := by
    classical
    by_cases hq : D.lower = q
    · subst q
      apply D.filtered p
      intro hz
      apply h
      simp [hz]
    · exact (h (Finsupp.single_eq_of_ne (Ne.symm hq))).elim
  smooth r l p q := by
    classical
    by_cases hq : D.lower = q
    · subst q
      simpa only [Finsupp.single_eq_same] using (hf r l).mul contDiffOn_const
    · simpa only [Finsupp.single_eq_of_ne (Ne.symm hq)] using
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0))
  classical mu r p hmu := by simp [hf0 mu r hmu]
  unit mu r l _ := by simp [D.unit]
  linear_add mu r l p q := by simp only [map_add, mul_add, Finsupp.single_add]
  linear_smul mu r l c p := by
    rw [map_smul, Finsupp.smul_single]
    congr 1
    simp only [smul_eq_mul]
    ring

def MixingGraphOrder (K : CompositeMixing G) : Prop :=
  ∀ mu r l p, 0 < mu → r < 2*l → K.coefficient mu r l p = 0

theorem addMixing_graph (K H : CompositeMixing G)
    (hK : MixingGraphOrder K) (hH : MixingGraphOrder H) : MixingGraphOrder (addMixing K H) := by
  intro mu r l p hmu hrl
  simp only [addMixing, hK mu r l p hmu hrl, hH mu r l p hmu hrl, add_zero]

theorem scaleMixing_graph (K : CompositeMixing G) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (hK : MixingGraphOrder K) :
    MixingGraphOrder (scaleMixing K a ha) := by
  intro mu r l p hmu hrl
  simp only [scaleMixing, hK mu r l p hmu hrl, smul_zero]

theorem subMixing_graph (K H : CompositeMixing G)
    (hK : MixingGraphOrder K) (hH : MixingGraphOrder H) : MixingGraphOrder (subMixing K H) :=
  addMixing_graph K _ hK (scaleMixing_graph H _ _ hH)

theorem delayMixing_graph (K : CompositeMixing G) (hK : MixingGraphOrder K) :
    MixingGraphOrder (delayMixing K) := by
  intro mu r l p hmu hrl
  obtain r | r | r := r <;> cases l
  all_goals first | rfl | exact hK mu _ _ p hmu (by omega)

theorem inputMixing_graph (K : CompositeMixing G) (D : Direction G)
    (hK : MixingGraphOrder K) : MixingGraphOrder (inputMixing K D) := by
  intro mu r l p hmu hrl
  simp only [inputMixing, hK mu r l D.lower hmu hrl, smul_zero]

def correctionRate (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (mu : ℝ) (r l : ℕ) : ℝ :=
  (if r = 2 ∧ l = 1 then mu * deriv a mu else 0) +
    match r, l with
    | r+1, l+1 => 2*a mu*beta r l
    | _, _ => 0

theorem correctionRate_smooth (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (r l : ℕ) :
    ContDiffOn ℝ ∞ (fun mu => correctionRate beta a mu r l) (Set.Ioi 0) := by
  have hd : ContDiffOn ℝ ∞ (deriv a) (Set.Ioi 0) :=
    ha.deriv_of_isOpen isOpen_Ioi (by simp)
  unfold correctionRate
  apply ContDiffOn.add
  · split_ifs
    · exact contDiffOn_id.mul hd
    · exact contDiffOn_const
  · cases r <;> cases l
    all_goals first | exact contDiffOn_const |
      exact (contDiffOn_const.mul ha).mul contDiffOn_const

theorem correctionRate_classical (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (mu : ℝ) (r : ℕ) : correctionRate beta a mu r 0 = 0 := by
  cases r <;> simp [correctionRate]

theorem correctionRate_graph (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (hb : ∀ r l, r < 2*l+1 → beta r l = 0) (mu : ℝ) (r l : ℕ)
    (hrl : r < 2*l) : correctionRate beta a mu r l = 0 := by
  have hz : ¬ (r = 2 ∧ l = 1) := by omega
  unfold correctionRate
  rw [if_neg hz, zero_add]
  cases r with
  | zero => rfl
  | succ r =>
    cases l with
    | zero => rfl
    | succ l =>
      change 2*a mu*beta r l = 0
      rw [hb r l (by omega), mul_zero]

def rateMixing (D : Direction G) (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) : CompositeMixing G :=
  rankMixing D (correctionRate beta a) (correctionRate_smooth beta a ha)
    (fun mu r _ => correctionRate_classical beta a mu r)

theorem rateMixing_graph (D : Direction G) (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (hb : ∀ r l, r < 2*l+1 → beta r l = 0) : MixingGraphOrder (rateMixing D beta a ha) := by
  intro mu r l p _ hrl
  simp only [rateMixing, rankMixing, correctionRate_graph beta a hb mu r l hrl,
    zero_mul, Finsupp.single_zero]

/-- Column-label convention. The quadratic cross term is retained even when
the correction preserves (rather than strictly lowers) intrinsic dimension. -/
def changeMixing (K : CompositeMixing G) (D : Direction G) (hq : D.weight D.lower = 0)
    (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) : CompositeMixing G :=
  subMixing
    (subMixing
      (subMixing
        (addMixing K (scaleMixing (delayMixing (inputMixing K D)) a ha))
        (scaleMixing (delayMixing (differenceMixing K D hq)) a ha))
      (scaleMixing (delayMixing (delayMixing (differenceMixing (inputMixing K D) D hq)))
        (fun mu => a mu*a mu) (ha.mul ha)))
    (rateMixing D beta a ha)

theorem changeMixing_graph (K : CompositeMixing G) (D : Direction G)
    (hq : D.weight D.lower = 0) (beta : ScalarCoefficients) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (hK : MixingGraphOrder K)
    (hb : ∀ r l, r < 2*l+1 → beta r l = 0) :
    MixingGraphOrder (changeMixing K D hq beta a ha) := by
  apply subMixing_graph
  · apply subMixing_graph
    · apply subMixing_graph
      · exact addMixing_graph K _ hK
          (scaleMixing_graph _ a ha (delayMixing_graph _ (inputMixing_graph K D hK)))
      · exact scaleMixing_graph _ a ha
          (delayMixing_graph _ (differenceMixing_graph K D hq hK))
    · exact scaleMixing_graph _ _ _
        (delayMixing_graph _ (delayMixing_graph _
          (differenceMixing_graph _ D hq (inputMixing_graph K D hK))))
  · exact rateMixing_graph D beta a ha hb

#print axioms addMixing
#print axioms scaleMixing
#print axioms subMixing_coefficient
#print axioms delayMixing
#print axioms inputMixing
#print axioms rankMixing
#print axioms addMixing_graph
#print axioms scaleMixing_graph
#print axioms subMixing_graph
#print axioms delayMixing_graph
#print axioms inputMixing_graph
#print axioms correctionRate_smooth
#print axioms correctionRate_classical
#print axioms correctionRate_graph
#print axioms rateMixing
#print axioms rateMixing_graph
#print axioms changeMixing
#print axioms changeMixing_graph
end YMYMG.MixingTransport
