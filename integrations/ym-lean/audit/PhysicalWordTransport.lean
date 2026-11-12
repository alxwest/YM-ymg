import DictionaryInsertionTransport
import WordJetAlgebra
import YangMills.LocalWardFlowFamily

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Transport of the actual invariant vacuum words. The argument preserves
the original insertion slots, continuum distributions and exact primitive.
It does not assume nullity on elementary external legs or on coincidences. -/
noncomputable section
open scoped BigOperators
namespace YMYMG.DictionaryRenormalization
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YMYMG.CouplingTaylor YMYMG.WordJet
variable {G : CompactSimpleGaugeGroup} {lift : QuantumObservableLift G}
variable {B : InvariantForm G} {e : ColorFrame B}
  {anomaly : ℝ → LocalAnomalyCoefficients G} {Q : QuantumWardLimit G}

abbrev WordState (G : CompactSimpleGaugeGroup) (arity : ℕ) :=
  Fin arity → LocalMonomial G

def slotMap (lift : QuantumObservableLift G) {arity : ℕ} (i : Fin arity)
    (p : InvariantInsertionLabel G) :
    (WordState G arity → Jet) →ₗ[ℂ] (WordState G arity → Jet) :=
  insertionMap (monomialsBelow G (intrinsicEngineeringDimension p + 1))
    (physicalJets lift p) (fun current m => Function.update current i m)

theorem slotMap_delay {arity : ℕ} (i : Fin arity) (p : InvariantInsertionLabel G)
    (F : WordState G arity → Jet) :
    slotMap lift i p (delayMap _ F) = delayMap _ (slotMap lift i p F) :=
  insertionMap_delay _ _ _ _

theorem slotMap_change (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ)
    {arity : ℕ} (i : Fin arity) (p : InvariantInsertionLabel G)
    (F : WordState G arity → Jet) :
    slotMap (change lift D a) i p F = slotMap lift i p F +
      ((a * D.weight p : ℝ) : ℂ) • delayMap _ (slotMap lift i D.lower F) := by
  funext current order loop
  simpa only [slotMap, insertionMap, continuumValue, delayMap,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using!
    (continuumValue_change h D a
      (fun m r l => F (Function.update current i m) r l) p order loop)

def wordMap (lift : QuantumObservableLift G) {arity : ℕ} :
    List (Fin arity × InvariantInsertionLabel G) →
      (WordState G arity → Jet) →ₗ[ℂ] (WordState G arity → Jet)
  | [] => LinearMap.id
  | (i,p) :: rest => (slotMap lift i p).comp (wordMap lift rest)

theorem wordMap_append {arity : ℕ}
    (xs ys : List (Fin arity × InvariantInsertionLabel G)) :
    wordMap lift (xs ++ ys) = (wordMap lift xs).comp (wordMap lift ys) := by
  induction xs with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨i,p⟩
    simp only [List.cons_append, wordMap, ih, LinearMap.comp_assoc]

theorem wordMap_delay {arity : ℕ}
    (xs : List (Fin arity × InvariantInsertionLabel G))
    (F : WordState G arity → Jet) :
    wordMap lift xs (delayMap _ F) = delayMap _ (wordMap lift xs F) := by
  induction xs with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨i,p⟩
    simp only [wordMap, LinearMap.comp_apply, ih, slotMap_delay]

theorem wordMap_change_head (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ)
    {arity : ℕ} (initial rest : List (Fin arity × InvariantInsertionLabel G))
    (i : Fin arity) (p : InvariantInsertionLabel G) (F : WordState G arity → Jet) :
    wordMap lift initial (wordMap (change lift D a) ((i,p)::rest) F) =
      wordMap lift (initial ++ [(i,p)]) (wordMap (change lift D a) rest F) +
      ((a * D.weight p : ℝ) : ℂ) • delayMap _
        (wordMap lift (initial ++ [(i,D.lower)]) (wordMap (change lift D a) rest F)) := by
  simp only [wordMap_append, wordMap, LinearMap.comp_apply, LinearMap.id_apply]
  rw [slotMap_change h D a, map_add, map_smul, wordMap_delay]

/-- Any property stable under finite sums, scalars and the (2,1) delay
passes from all original words to the changed words with the same slots. -/
theorem wordMap_transfer (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ)
    {arity : ℕ} (F : WordState G arity → Jet)
    (P : (WordState G arity → Jet) → Prop)
    (hadd : ∀ f g, P f → P g → P (f+g))
    (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
    (hdelay : ∀ f, P f → P (delayMap _ f))
    (slots : List (Fin arity))
    (hOld : ∀ xs : List (Fin arity × InvariantInsertionLabel G),
      xs.map Prod.fst = slots → P (wordMap lift xs F))
    (xs : List (Fin arity × InvariantInsertionLabel G))
    (hx : xs.map Prod.fst = slots) :
    P (wordMap (change lift D a) xs F) := by
  have aux (rest : List (Fin arity × InvariantInsertionLabel G)) :
      ∀ initial : List (Fin arity × InvariantInsertionLabel G),
      (initial ++ rest).map Prod.fst = slots →
      P (wordMap lift initial (wordMap (change lift D a) rest F)) := by
    induction rest with
    | nil =>
      intro initial hp
      exact hOld initial (by simpa using hp)
    | cons head rest ih =>
      rcases head with ⟨i,p⟩
      intro initial hp
      rw [wordMap_change_head h D a]
      apply hadd
      · apply ih (initial ++ [(i,p)])
        simpa only [List.append_assoc, List.singleton_append] using hp
      · apply hsmul
        apply hdelay
        apply ih (initial ++ [(i,D.lower)])
        simpa only [List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append] using hp
  exact aux xs [] hx

/-- Recover the labels of any list with the same ordered position slots. -/
theorem labels_of_slots {n : ℕ} {α β : Type*} (slots : Fin n → α)
    (xs : List (α × β)) (h : xs.map Prod.fst = List.ofFn slots) :
    ∃ labels : Fin n → β, xs = List.ofFn (fun i => (slots i, labels i)) := by
  have hlen : xs.length = n := by
    have hh := congrArg List.length h
    simpa only [List.length_map, List.length_ofFn] using hh
  let labels : Fin n → β := fun i => (xs[i.val]'(by omega)).2
  refine ⟨labels, ?_⟩
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hlen)
  intro i hi hj
  have hi' : i < n := by omega
  have he := congrArg (fun ys : List α => ys[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, List.getElem?_ofFn, dif_pos hi'] at he
  have he' : (xs[i]).1 = slots ⟨i,hi'⟩ := Option.some.inj he
  simp only [List.getElem_ofFn]
  exact Prod.ext he' rfl

def nativeWordBase {arity : ℕ} (W : WardContinuumData G)
    (test : JointMomentumTest arity ([] : List (ExternalLeg G))) :
    WordState G arity → Jet :=
  fun current order loop => W.physical (.disconnected 0) order loop current [] test

theorem wordMap_native {arity : ℕ} (W : WardContinuumData G)
    (test : JointMomentumTest arity ([] : List (ExternalLeg G)))
    (xs : List (Fin arity × InvariantInsertionLabel G))
    (current : WordState G arity) (order loop : ℕ) :
    wordMap lift xs (nativeWordBase W test) current order loop =
      physicalLiftedWordExpansion W lift xs order loop current test := by
  induction xs generalizing current order loop with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨i,p⟩
    simp only [wordMap, LinearMap.comp_apply, slotMap, insertionMap,
      LinearMap.coe_mk, AddHom.coe_mk, convolve, ih, physicalLiftedWordExpansion,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      physicalJets, jet, physicalLiftCouplingCoefficient]

/-- The same generated exact primitive at slot zero. -/
def exactWordMap {n : ℕ} (Q : QuantumWardLimit G) (primitive : LocalMonomial G) :
    (WordState G (n+1) → Jet) →ₗ[ℂ] (WordState G (n+1) → Jet) :=
  insertionMap (monomialsBelow G (primitive.dimension + 2))
    (fun m order loop => quantumWardCouplingCoefficient Q order loop primitive m)
    (fun current m => Function.update current 0 m)

theorem exactWordMap_delay {n : ℕ} (Q : QuantumWardLimit G)
    (primitive : LocalMonomial G) (F : WordState G (n+1) → Jet) :
    exactWordMap Q primitive (delayMap _ F) =
      delayMap _ (exactWordMap Q primitive F) :=
  insertionMap_delay _ _ _ _

theorem exactWordMap_native {n : ℕ} (W : WardContinuumData G) (Q : QuantumWardLimit G)
    (primitive : LocalMonomial G) (spectators : Fin n → InvariantInsertionLabel G)
    (test : JointMomentumTest (n+1) ([] : List (ExternalLeg G))) (order loop : ℕ) :
    exactWordMap Q primitive
      (wordMap lift (List.ofFn fun i : Fin n => (i.succ, spectators i))
        (nativeWordBase W test)) (fun _ => 0) order loop =
      physicalExactInvariantWord W Q lift primitive spectators order loop test := by
  simp only [exactWordMap, insertionMap, LinearMap.coe_mk, AddHom.coe_mk,
    convolve, wordMap_native, physicalExactInvariantWord,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem delay_preserves_graph (f : Jet) (h : ∀ r l, r < 2*l → f r l = 0) :
    ∀ r l, r < 2*l → delay f r l = 0 := by
  intro r l hr
  obtain r | r | r := r <;> cases l
  all_goals first | rfl | exact h _ _ (by omega)

theorem delay_preserves_zero (f : Jet) (h : ∀ r l, f r l = 0) :
    ∀ r l, delay f r l = 0 := by
  intro r l
  cases l with
  | zero => obtain r | r | r := r <;> rfl
  | succ l =>
    obtain r | r | r := r
    · rfl
    · rfl
    · exact h r l

/-- The actual distributional graph-order field survives at every arity. -/
theorem physical_word_graph (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ)
    {W : WardContinuumData G}
    (hgraph : ∀ order loop n (labels : Fin n → InvariantInsertionLabel G),
      order < 2*loop → physicalInvariantWord W lift labels order loop = 0) :
    ∀ order loop n (labels : Fin n → InvariantInsertionLabel G),
      order < 2*loop → physicalInvariantWord W (change lift D a) labels order loop = 0 := by
  intro order loop n labels hor
  apply LinearMap.ext
  intro test
  let P : (WordState G n → Jet) → Prop :=
    fun F => ∀ r l, r < 2*l → F (fun _ => 0) r l = 0
  have hP : P (wordMap (change lift D a) (List.ofFn fun i => (i,labels i))
      (nativeWordBase W test)) := by
    refine wordMap_transfer h D a _ P ?_ ?_ ?_
      (List.ofFn fun i : Fin n => i) ?_ _ ?_
    · intro f g hf hg r l hr
      change f (fun _ => 0) r l + g (fun _ => 0) r l = 0
      simp only [hf r l hr, hg r l hr, add_zero]
    · intro c f hf r l hr
      change c * f (fun _ => 0) r l = 0
      simp only [hf r l hr, mul_zero]
    · intro f hf r l hr
      exact delay_preserves_graph (f (fun _ => 0)) hf r l hr
    · intro xs hxs
      obtain ⟨labs, rfl⟩ := labels_of_slots (fun i : Fin n => i) xs hxs
      intro r l hr
      rw [wordMap_native]
      simpa only [physicalInvariantWord, LinearMap.zero_apply] using!
        congrArg (fun T : JointMomentumDistribution n ([] : List (ExternalLeg G)) => T test)
          (hgraph r l n labs hr)
    · simp only [List.map_ofFn, Function.comp_def]
  change physicalLiftedWordExpansion W (change lift D a)
    (List.ofFn fun i => (i,labels i)) order loop (fun _ => 0) test = 0
  rw [← wordMap_native]
  exact hP order loop hor

/-- Nullity is transported only on the native domain: invariant spectators,
the same primitive and Q, no elementary legs, and separated compact tests. -/
theorem physical_word_null (h : lift.Compatible e anomaly Q) (D : Direction G) (a : ℝ)
    {W : WardContinuumData G} (hn : InvariantPhysicalNullIdentity W Q lift) :
    InvariantPhysicalNullIdentity W Q (change lift D a) := by
  refine ⟨hn.1, hn.2.1, ?_⟩
  intro primitive hp hghost hparity n spectators order loop test ht ho
  let P : (WordState G (n+1) → Jet) → Prop :=
    fun F => ∀ r l, exactWordMap Q primitive F (fun _ => 0) r l = 0
  have hP : P (wordMap (change lift D a) (List.ofFn fun i => (i.succ,spectators i))
      (nativeWordBase W test)) := by
    refine wordMap_transfer h D a _ P ?_ ?_ ?_
      (List.ofFn fun i : Fin n => i.succ) ?_ _ ?_
    · intro f g hf hg r l
      change exactWordMap Q primitive (f+g) (fun _ => 0) r l = 0
      rw [map_add]
      change exactWordMap Q primitive f (fun _ => 0) r l +
        exactWordMap Q primitive g (fun _ => 0) r l = 0
      simp only [hf r l, hg r l, add_zero]
    · intro c f hf r l
      change exactWordMap Q primitive (c • f) (fun _ => 0) r l = 0
      rw [map_smul]
      change c * exactWordMap Q primitive f (fun _ => 0) r l = 0
      simp only [hf r l, mul_zero]
    · intro f hf r l
      change exactWordMap Q primitive (delayMap _ f) (fun _ => 0) r l = 0
      rw [exactWordMap_delay]
      exact delay_preserves_zero (exactWordMap Q primitive f (fun _ => 0)) hf r l
    · intro xs hxs
      obtain ⟨labs, rfl⟩ := labels_of_slots (fun i : Fin n => i.succ) xs hxs
      intro r l
      rw [exactWordMap_native]
      exact hn.2.2 primitive hp hghost hparity n labs r l test ht ho
    · simp only [List.map_ofFn, Function.comp_def]
  rw [← exactWordMap_native]
  exact hP order loop

theorem physical_word_null_iff (h : lift.Compatible e anomaly Q)
    (D : Direction G) (a : ℝ) (hq : D.weight D.lower = 0) {W : WardContinuumData G} :
    InvariantPhysicalNullIdentity W Q (change lift D a) ↔
      InvariantPhysicalNullIdentity W Q lift := by
  constructor
  · intro hn
    have hb := physical_word_null (compatible h D a) D (-a) hn
    simpa only [change_inverse D a hq] using hb
  · exact physical_word_null h D a

theorem physical_word_graph_iff (h : lift.Compatible e anomaly Q)
    (D : Direction G) (a : ℝ) (hq : D.weight D.lower = 0) {W : WardContinuumData G} :
    (∀ order loop n (labels : Fin n → InvariantInsertionLabel G),
      order < 2*loop → physicalInvariantWord W (change lift D a) labels order loop = 0) ↔
    (∀ order loop n (labels : Fin n → InvariantInsertionLabel G),
      order < 2*loop → physicalInvariantWord W lift labels order loop = 0) := by
  constructor
  · intro hg
    have hb := physical_word_graph (compatible h D a) D (-a) hg
    simpa only [change_inverse D a hq] using hb
  · exact physical_word_graph h D a

/-- A complete native family is transported, assuming an original family.
The coefficient may depend on scale: this structure imposes the Ward and
physical-word conditions at each scale. Smooth scale-insertion/CS data are
separate and are not asserted here. -/
def changeFamily {S : FixedFlowSystem e} (family : LocalWardFlowFamily S)
    (D : Direction G) (a : RenormalizationScale → ℝ) : LocalWardFlowFamily S :=
  { family with
    lift := fun mu => change (family.lift mu) D (a mu)
    full_ward := fun mu => fullWardRestoration (family.full_ward mu) D (a mu)
    physical_word_null := fun mu =>
      physical_word_null (family.full_ward mu).same_dictionary D (a mu)
        (family.physical_word_null mu)
    physical_word_graph := fun mu =>
      physical_word_graph (family.full_ward mu).same_dictionary D (a mu)
        (family.physical_word_graph mu) }

theorem changeFamily_inverse {S : FixedFlowSystem e} (family : LocalWardFlowFamily S)
    (D : Direction G) (a : RenormalizationScale → ℝ) (hq : D.weight D.lower = 0) :
    changeFamily (changeFamily family D a) D (fun mu => -a mu) = family := by
  cases family
  simp only [changeFamily, change_inverse D _ hq]

/-- The changed family is an equivalent presentation of an existing family,
not a way to construct a family from the October existence statement. -/
def changeFamilyEquiv {S : FixedFlowSystem e} (D : Direction G)
    (a : RenormalizationScale → ℝ) (hq : D.weight D.lower = 0) :
    LocalWardFlowFamily S ≃ LocalWardFlowFamily S where
  toFun family := changeFamily family D a
  invFun family := changeFamily family D (fun mu => -a mu)
  left_inv family := changeFamily_inverse family D a hq
  right_inv family := by
    simpa only [neg_neg] using changeFamily_inverse family D (fun mu => -a mu) hq

#print axioms physical_word_null_iff
#print axioms physical_word_graph_iff
#print axioms changeFamily
#print axioms changeFamily_inverse
#print axioms changeFamilyEquiv
#print axioms wordMap_native
#print axioms exactWordMap_delay
#print axioms exactWordMap_native
#print axioms delay_preserves_graph
#print axioms delay_preserves_zero
#print axioms physical_word_graph
#print axioms physical_word_null

#print axioms slotMap_delay
#print axioms slotMap_change
#print axioms wordMap_append
#print axioms wordMap_delay
#print axioms wordMap_change_head
#print axioms wordMap_transfer
#print axioms labels_of_slots
end YMYMG.DictionaryRenormalization
