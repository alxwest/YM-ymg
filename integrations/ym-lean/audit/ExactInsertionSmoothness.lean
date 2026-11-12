import NativeMixingTransport
import YangMills.FullBVIntegratedHamiltonian

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-! Coupling smoothness of the actual generated quantum-exact insertion.
No topology on the algebraic jet space is assumed: each scalar extraction
of the finite master-action polynomial is treated directly. -/
noncomputable section
open scoped BigOperators ContDiff
namespace YMYMG.ExactTransport
open YangMills YangMills.Perturbative YangMills.PerturbativeFlow
open YangMills.ScaleInsertion YangMills.Legendre YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

theorem characteristic_add (S T : JetAlgebra G) (field : ExternalLeg G) :
    stCharacteristic (S+T) field = stCharacteristic S field + stCharacteristic T field := by
  cases field <;> simp only [stCharacteristic, rightEuler_add]
  abel

theorem characteristic_smul (S : JetAlgebra G) (c : ℂ) (field : ExternalLeg G) :
    stCharacteristic (c • S) field = c • stCharacteristic S field := by
  cases field <;> simp [stCharacteristic, rightEuler_smul]

theorem localST_action_add (S T P : JetAlgebra G) :
    localST (S+T) P = localST S P + localST T P := by
  simp only [localST_finsum_jet, prolongedST, characteristic_add,
    totalDerivatives_add, add_mul]
  exact finsum_add_distrib (jetSummands_finite _ P) (jetSummands_finite _ P)

theorem localST_action_smul (S P : JetAlgebra G) (c : ℂ) :
    localST (c • S) P = c • localST S P := by
  simp only [localST_finsum_jet, prolongedST, characteristic_smul,
    totalDerivatives_smul, smul_mul_assoc]
  exact ((c • LinearMap.id : JetAlgebra G →ₗ[ℂ] JetAlgebra G).toAddMonoidHom.map_finsum
    (jetSummands_finite _ P)).symm

def actionLinear (P : JetAlgebra G) : JetAlgebra G →ₗ[ℂ] JetAlgebra G where
  toFun S := localST S P
  map_add' S T := localST_action_add S T P
  map_smul' c S := localST_action_smul S P c

theorem vertices_scalar_smooth (T : JetAlgebra G →ₗ[ℂ] ℂ) (vertices : List (LocalVertex G)) :
    ContDiff ℝ ∞ (fun g : ℝ => T (densityOfVertices g vertices)) := by
  induction vertices with
  | nil => simpa only [densityOfVertices, List.map_nil, List.sum_nil, map_zero] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)))
  | cons v vs ih =>
    simp only [densityOfVertices, List.map_cons, List.sum_cons, map_add, densityOfVertex, map_smul]
    exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.pow v.couplingOrder)).mul
      contDiff_const).add ih

theorem classicalWard_smooth {B : InvariantForm G} (e : ColorFrame B)
    (input output : LocalMonomial G) :
    ContDiff ℝ ∞ (fun g => densityMonomialCoefficient
      (classicalLocalSTDensity e g (normalizedMonomialDensity input)) output) := by
  let T : JetAlgebra G →ₗ[ℂ] ℂ := augmentation.comp
    ((externalJetDerivative (output.orderedJets.map fullBVJet)).comp
      (actionLinear (normalizedMonomialDensity input)))
  change ContDiff ℝ ∞ (fun g => T (masterActionDensity e g))
  simp only [masterActionDensity, map_add, interactionDensity]
  exact contDiff_const.add (vertices_scalar_smooth T _)

theorem generatedWard_smooth {B : InvariantForm G} (e : ColorFrame B)
    {L : ℝ → InsertedFlowFamily G} (transport : SameTheoryWardTransportData e L)
    (loop : ℕ) (UV : ℝ) (input output : LocalMonomial G) :
    ContDiff ℝ ∞ (fun g => generatedQuantumWardCoefficient e g (transport.coefficient g)
      loop UV input output) := by
  unfold generatedQuantumWardCoefficient
  apply ContDiff.add
  · split_ifs
    · exact classicalWard_smooth e input output
    · exact contDiff_const
  · rw [show (fun g => transport.coefficient g loop UV input output) =
        (fun g : ℝ => if input.legs.length ≤ output.legs.length + 2*loop then
          (g : ℂ)^(output.legs.length+2*loop-input.legs.length) *
            transport.coefficient 1 loop UV input output else 0) from
        funext (fun g => transport.coefficient_graph_grading g loop UV input output)]
    split_ifs
    · exact (Complex.ofRealCLM.contDiff.pow _).mul contDiff_const
    · exact contDiff_const

theorem primitive_coupling_smooth {degree offset : ℕ}
    (P : LocalScalePrimitive G degree offset) (mu : ℝ) (loop : ℕ) (m : LocalMonomial G) :
    ContDiff ℝ ∞ (fun g => P.coefficient mu g loop m) := by
  rw [show (fun g => P.coefficient mu g loop m) =
      (fun g : ℝ => if offset ≤ m.legs.length+2*loop then
        (g : ℂ)^(m.legs.length+2*loop-offset)*P.coefficient mu 1 loop m else 0) from
      funext (fun g => P.graph_power mu g loop m)]
  split_ifs
  · exact (Complex.ofRealCLM.contDiff.pow _).mul contDiff_const
  · exact contDiff_const

theorem primitive_support_at_one {degree offset : ℕ}
    (P : LocalScalePrimitive G degree offset) (mu g : ℝ) (loop : ℕ) :
    (P.coefficient mu g loop).support ⊆ (P.coefficient mu 1 loop).support := by
  intro m hm
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have hn := Finsupp.mem_support_iff.mp hm
  apply hn
  rw [P.graph_power, hz]
  simp

theorem exactInsertion_fixed_support {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (L : ℝ → ℝ → InsertedFlowFamily G)
    {degree offset : ℕ} (P : LocalScalePrimitive G degree offset)
    (mu g : ℝ) (x : Spacetime) (loop : ℕ) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    quantumExactInsertion e anomaly L P mu g x loop IR UV legs q =
      ∑ a : Fin (loop+1), ∑ b : Fin (loop-a.val+1),
        ∑ input ∈ (P.coefficient mu 1 a.val).support,
          ∑ output ∈ monomialsBelow G (input.dimension+2),
            P.coefficient mu g a.val input *
              generatedQuantumWardCoefficient e g (anomaly mu g) b.val UV input output *
                L mu g [⟨output,x⟩] (loop-a.val-b.val) IR UV legs q := by
  unfold quantumExactInsertion
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact Finsupp.sum_of_support_subset _ (primitive_support_at_one P mu g a.val) _
    (by intro input _; simp)

theorem exactInsertion_smooth {B : InvariantForm G} (e : ColorFrame B)
    (anomaly : ℝ → ℝ → LocalAnomalyCoefficients G) (L : ℝ → ℝ → InsertedFlowFamily G)
    {degree offset : ℕ} (P : LocalScalePrimitive G degree offset)
    (mu : ℝ) (transport : SameTheoryWardTransportData e (L mu))
    (he : anomaly mu = transport.coefficient) (x : Spacetime) (loop : ℕ) (IR UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (hL : ∀ input l, ContDiff ℝ ∞ (fun g => L mu g input l IR UV legs q)) :
    ContDiff ℝ ∞ (fun g => quantumExactInsertion e anomaly L P mu g x loop IR UV legs q) := by
  simp only [exactInsertion_fixed_support, he]
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  apply ContDiff.sum
  intro input _
  apply ContDiff.sum
  intro output _
  exact ((primitive_coupling_smooth P mu a.val input).mul
    (generatedWard_smooth e transport b.val UV input output)).mul (hL _ _)

theorem family_exactInsertion_smooth {B : InvariantForm G} {e : ColorFrame B}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S)
    {degree offset : ℕ} (P : LocalScalePrimitive G degree offset)
    (mu : ℝ) (hmu : 0 < mu) (x : Spacetime) (loop : ℕ) (s : CutoffScales)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    ContDiff ℝ ∞ (fun g => quantumExactInsertion e
      (positiveScaleExtension S.referenceScale (fun scale => (family.singleTransport scale).coefficient))
      S.insertions P mu g x loop s.infrared s.ultraviolet legs q) := by
  apply exactInsertion_smooth e _ _ P mu (family.singleTransport ⟨mu,hmu⟩)
    (by simp only [positiveScaleExtension, dif_pos hmu])
  intro input l
  simpa only [Function.comp_def] using!
    ((S.insertion_equations mu hmu).single_joint_smooth input l s.infrared s.ultraviolet legs
      s.infrared_pos s.ordered).comp (contDiff_id.prodMk contDiff_const)

#print axioms characteristic_add
#print axioms characteristic_smul
#print axioms localST_action_add
#print axioms localST_action_smul
#print axioms actionLinear
#print axioms vertices_scalar_smooth
#print axioms classicalWard_smooth
#print axioms generatedWard_smooth
#print axioms primitive_coupling_smooth
#print axioms primitive_support_at_one
#print axioms exactInsertion_fixed_support
#print axioms exactInsertion_smooth
#print axioms family_exactInsertion_smooth
end YMYMG.ExactTransport
