import GeneralResults.NuclearExtensionComplex
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Prototype for the scalar/component Schwartz kernel API. -/

noncomputable section
open scoped SchwartzMap BigOperators
open GaussianField

namespace EuclideanField

/-- Finite scalar component tests with the product Schwartz topology. -/
abbrev RealTest (d : ℕ) (I : Type*) := I → 𝓢(EuclideanSpace ℝ (Fin d), ℝ)

abbrev ComplexTest (d : ℕ) (I : Type*) := I → 𝓢(EuclideanSpace ℝ (Fin d), ℂ)

/-- Degree `n` joint kernels, indexed by words of component labels. -/
abbrev JointTest (d : ℕ) (I : Type*) (n : ℕ) :=
  (Fin n → I) → 𝓢(Fin n → EuclideanSpace ℝ (Fin d), ℂ)

end EuclideanField

namespace SchwartzMap

/-- A domain equivalence acts continuously and complex linearly by pullback. -/
def complexDomCongr {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : D ≃L[ℝ] E) :
    𝓢(E, ℂ) ≃L[ℂ] 𝓢(D, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLMOfContinuousLinearEquiv ℂ g)
    (compCLMOfContinuousLinearEquiv ℂ g.symm)
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.apply_symm_apply x))
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.symm_apply_apply x))

@[simp] theorem complexDomCongr_apply {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : D ≃L[ℝ] E)
    (f : 𝓢(E, ℂ)) (x : D) : complexDomCongr g f x = f (g x) := rfl

/-- Euclidean and Pi coordinate topologies are related by an actual CLE. -/
def euclideanPiEquiv (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

/-- Apply the Euclidean/Pi coordinate change separately in every slot. -/
def jointEuclideanPiEquiv (d n : ℕ) :
    (Fin n → EuclideanSpace ℝ (Fin d)) ≃L[ℝ] (Fin n → Fin d → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun _ => euclideanPiEquiv d

/-- Product tensors commute with factorwise domain changes. -/
theorem complexDomCongr_product {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : D ≃L[ℝ] E)
    {n : ℕ} (fs : Fin n → 𝓢(E, ℂ)) :
    complexDomCongr (ContinuousLinearEquiv.piCongrRight fun _ : Fin n => g)
      (GaussianField.complexProductTensor fs) =
        GaussianField.complexProductTensor (fun i => complexDomCongr g (fs i)) := by
  ext x
  simp [GaussianField.complexProductTensor_apply]

/-- Transfer the product-aware nuclear extension along any real domain CLE. -/
theorem schwartz_nuclear_extension_of_equiv {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] {d n : ℕ}
    (g : D ≃L[ℝ] (Fin (d + 1) → ℝ))
    (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => 𝓢(D, ℂ)) ℂ) :
    ∃! (W : 𝓢(Fin n → D, ℂ) →L[ℂ] ℂ),
      ∀ fs, W (GaussianField.complexProductTensor fs) = Φ fs := by
  let T := complexDomCongr g
  let P := complexDomCongr (ContinuousLinearEquiv.piCongrRight fun _ : Fin n => g)
  obtain ⟨W, hW, hUnique⟩ := GaussianField.schwartz_nuclear_extension d n
    (Φ.compContinuousLinearMap fun _ => T.toContinuousLinearMap)
  have hP (fs : Fin n → 𝓢(D, ℂ)) :
      P.symm (GaussianField.complexProductTensor fs) =
        GaussianField.complexProductTensor (fun i => T.symm (fs i)) := by
    apply P.injective
    rw [P.apply_symm_apply]
    change _ = complexDomCongr _ _
    rw [complexDomCongr_product]
    congr 1
    funext i
    exact (T.apply_symm_apply (fs i)).symm
  refine ⟨W.comp P.symm.toContinuousLinearMap, ?_, ?_⟩
  · intro fs
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hP, hW,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact T.apply_symm_apply (fs i)
  · intro V hV
    have hVP : V.comp P.toContinuousLinearMap = W := hUnique _ (fun fs => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      change V (complexDomCongr _ _) = _
      rw [complexDomCongr_product, hV]
      rfl)
    ext f
    have := congrArg (fun L : 𝓢(Fin n → Fin (d + 1) → ℝ, ℂ) →L[ℂ] ℂ =>
      L (P.symm f)) hVP
    simpa using this

/-- Scalar Schwartz extension on Euclidean spacetime, with the Pi-norm transport explicit. -/
theorem schwartz_nuclear_extension_euclidean {d n : ℕ} (hd : 0 < d)
    (Φ : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ℂ) :
    ∃! (W : 𝓢(Fin n → EuclideanSpace ℝ (Fin d), ℂ) →L[ℂ] ℂ),
      ∀ fs, W (GaussianField.complexProductTensor fs) = Φ fs := by
  cases d with
  | zero => omega
  | succ d => exact schwartz_nuclear_extension_of_equiv (euclideanPiEquiv (d + 1)) Φ

end SchwartzMap

namespace EuclideanField

/-- Elementary joint kernels are the actual pointwise external products. -/
def jointProduct {d n : ℕ} {I : Type*} (fs : Fin n → ComplexTest d I) :
    JointTest d I n := fun α =>
  GaussianField.complexProductTensor (fun i => fs i (α i))

@[simp] theorem jointProduct_apply {d n : ℕ} {I : Type*}
    (fs : Fin n → ComplexTest d I) (α : Fin n → I)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    jointProduct fs α x = ∏ i, fs i (α i) (x i) :=
  GaussianField.complexProductTensor_apply _ _

theorem jointProduct_zero_apply {d : ℕ} {I : Type*}
    (fs : Fin 0 → ComplexTest d I) (α : Fin 0 → I)
    (x : Fin 0 → EuclideanSpace ℝ (Fin d)) : jointProduct fs α x = 1 := by
  simp

/-- Positive degree joint kernels vanish for an empty component index. -/
theorem jointTest_eq_zero_of_isEmpty {d n : ℕ} {I : Type*} [IsEmpty I]
    (hn : 0 < n) (h : JointTest d I n) : h = 0 := by
  funext α
  exact isEmptyElim (α ⟨0, hn⟩)

end EuclideanField

namespace SchwartzMap

/-- Schwartz functions on a zero-fold product form the scalar field. -/
def emptyProductEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    𝓢(Fin 0 → E, ℂ) ≃L[ℂ] ℂ := by
  let ev : 𝓢(Fin 0 → E, ℂ) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ (0 : Fin 0 → E)).comp
      (toBoundedContinuousFunctionCLM ℂ (Fin 0 → E) ℂ)
  let one : 𝓢(Fin 0 → E, ℂ) :=
    GaussianField.complexProductTensor (fun i : Fin 0 => Fin.elim0 i)
  let inv : ℂ →L[ℂ] 𝓢(Fin 0 → E, ℂ) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight one
  exact ContinuousLinearEquiv.equivOfInverse ev inv
    (fun f => by
      ext x
      simp only [ev, inv, one, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
        BoundedContinuousFunction.evalCLM_apply, toBoundedContinuousFunctionCLM_apply,
        smul_apply, GaussianField.complexProductTensor_apply, Finset.univ_eq_empty,
        Finset.prod_empty, smul_eq_mul, mul_one]
      exact congrArg f (Subsingleton.elim _ _))
    (fun z => by simp [ev, inv, one, GaussianField.complexProductTensor_apply])

end SchwartzMap

namespace EuclideanField

/-- Degree zero is scalar even when the component space is zero. -/
def jointTestZeroEquiv (d : ℕ) (I : Type*) : JointTest d I 0 ≃L[ℂ] ℂ :=
  (ContinuousLinearEquiv.funUnique (Fin 0 → I) ℂ
    𝓢(Fin 0 → EuclideanSpace ℝ (Fin d), ℂ)).trans
    (SchwartzMap.emptyProductEquiv (EuclideanSpace ℝ (Fin d)))

/-- Products with a single component per slot have precisely one nonzero word. -/
theorem jointProduct_single {d n : ℕ} {I : Type*} [DecidableEq I]
    (α : Fin n → I) (fs : Fin n → 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    jointProduct (fun i => Pi.single (α i) (fs i)) =
      Pi.single α (GaussianField.complexProductTensor fs) := by
  classical
  funext β
  by_cases h : β = α
  · subst β
    ext x
    simp [jointProduct_apply, GaussianField.complexProductTensor_apply]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    ext x
    simp only [jointProduct_apply, Pi.single_eq_of_ne h, zero_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Pi.single_eq_of_ne hi]

/-- Every continuous multilinear component functional is a unique joint distribution. -/
theorem joint_nuclear_extension {d n : ℕ} {I : Type*} [Fintype I] (hd : 0 < d)
    (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexTest d I) ℂ) :
    ∃! (W : JointTest d I n →L[ℂ] ℂ), ∀ fs, W (jointProduct fs) = Φ fs := by
  classical
  let ι (α : Fin n → I) (i : Fin n) :=
    ContinuousLinearMap.single ℂ
      (fun _ : I => 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (α i)
  choose W hW hUnique using (fun α : Fin n → I =>
    SchwartzMap.schwartz_nuclear_extension_euclidean hd
      (Φ.compContinuousLinearMap (ι α)))
  let V : JointTest d I n →L[ℂ] ℂ :=
    ∑ α, (W α).comp (ContinuousLinearMap.proj α)
  refine ⟨V, ?_, ?_⟩
  · intro fs
    simp only [V, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, jointProduct]
    simp_rw [hW]
    have hh := Φ.map_sum (fun i j => Pi.single j (fs i j))
    have heq : (fun i => ∑ j, Pi.single j (fs i j)) = fs := by
      funext i j
      simp
    simpa [ι, ContinuousMultilinearMap.compContinuousLinearMap_apply, heq] using hh.symm
  · intro V' hV'
    have hs (α : Fin n → I) :
        V'.comp (ContinuousLinearMap.single ℂ
          (fun _ : Fin n → I => 𝓢(Fin n → EuclideanSpace ℝ (Fin d), ℂ)) α) = W α := by
      apply hUnique α
      intro fs
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
        ← jointProduct_single, hV', ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ι]
    ext h
    have heq : h = ∑ α, Pi.single α (h α) := by ext α x; simp
    have hi (α : Fin n → I) : V' (Pi.single α (h α)) = W α (h α) :=
      congrArg (fun L : 𝓢(Fin n → EuclideanSpace ℝ (Fin d), ℂ) →L[ℂ] ℂ => L (h α)) (hs α)
    calc V' h = V' (∑ α, Pi.single α (h α)) := congrArg V' heq
      _ = ∑ α, W α (h α) := by simp only [map_sum, hi]
      _ = V h := by simp [V]

end EuclideanField

namespace SchwartzMap

/-- Finite linear combinations of genuine pointwise scalar external products. -/
def productSpan (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] (n : ℕ) :
    Submodule ℂ 𝓢(Fin n → D, ℂ) :=
  Submodule.span ℂ (Set.range (@GaussianField.complexProductTensor D _ _ n))

/-- The product-aware Hermite expansion converges in the Schwartz topology. -/
theorem ofReal_mem_productSpan_closure {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [Nontrivial D] [MeasurableSpace D] [BorelSpace D] {n : ℕ} (hn : 0 < n)
    (f : 𝓢(Fin n → D, ℝ)) :
    postcompCLM Complex.ofRealCLM f ∈ (productSpan D n).topologicalClosure := by
  let e := GaussianField.productRapidDecayEquiv (D := D) n hn
  let ι : 𝓢(Fin n → D, ℝ) →L[ℝ] 𝓢(Fin n → D, ℂ) :=
    postcompCLM Complex.ofRealCLM
  have hb (m : ℕ) : ι (e.symm (RapidDecaySeq.basisVec m)) ∈ productSpan D n := by
    apply Submodule.subset_span
    refine ⟨fun i => postcompCLM Complex.ofRealCLM
      (DyninMityaginSpace.basis (E := 𝓢(D, ℝ))
        (GaussianField.productBasisIndices (D := D) n hn m i)), ?_⟩
    ext x
    simp only [GaussianField.complexProductTensor_apply, postcompCLM_apply,
      Complex.ofRealCLM_apply, ← Complex.ofReal_prod]
    congr 1
    exact (GaussianField.productRapidDecayEquiv_symm_basisVec_isProductHermite n hn m x).symm
  have hs := (RapidDecaySeq.hasSum_basisVec (e f)).mapL
    (ι.comp e.symm.toContinuousLinearMap)
  have hs' : HasSum (fun m => (e f).val m • ι (e.symm (RapidDecaySeq.basisVec m))) (ι f) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_smul,
      e.symm_apply_apply] using hs
  apply (productSpan D n).isClosed_topologicalClosure.mem_of_tendsto hs'
  filter_upwards [] with s
  apply Submodule.sum_mem
  intro m hm
  exact ((productSpan D n).topologicalClosure.restrictScalars ℝ).smul_mem _
    ((productSpan D n).le_topologicalClosure (hb m))

/-- Genuine scalar products span a dense subspace in every degree. -/
theorem dense_productSpan {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [Nontrivial D] [MeasurableSpace D] [BorelSpace D] (n : ℕ) :
    Dense (productSpan D n : Set 𝓢(Fin n → D, ℂ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f hf
  cases n with
  | zero =>
    have h : f = f 0 • GaussianField.complexProductTensor
        (fun i : Fin 0 => Fin.elim0 i : Fin 0 → 𝓢(D, ℂ)) := by
      ext x
      simp only [smul_apply, GaussianField.complexProductTensor_apply,
        Finset.univ_eq_empty, Finset.prod_empty, smul_eq_mul, mul_one]
      exact congrArg f (Subsingleton.elim _ _)
    rw [h]
    apply Submodule.smul_mem
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨_, rfl⟩
  | succ n =>
    let fr := postcompCLM Complex.reCLM f
    let fi := postcompCLM Complex.imCLM f
    have h : f = postcompCLM Complex.ofRealCLM fr +
        Complex.I • postcompCLM Complex.ofRealCLM fi := by
      ext x
      simp only [add_apply, smul_apply, postcompCLM_apply, Complex.ofRealCLM_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, fr, fi]
      rw [mul_comm]
      exact (Complex.re_add_im (f x)).symm
    rw [h]
    exact Submodule.add_mem _ (ofReal_mem_productSpan_closure (Nat.succ_pos n) fr)
      (Submodule.smul_mem _ _ (ofReal_mem_productSpan_closure (Nat.succ_pos n) fi))

end SchwartzMap

namespace EuclideanField

/-- The polynomial test domain, viewed as a subspace of full joint Schwartz kernels. -/
def jointProductSpan (d : ℕ) (I : Type*) [Fintype I] (n : ℕ) :
    Submodule ℂ (JointTest d I n) :=
  Submodule.span ℂ (Set.range (@jointProduct d n I))

/-- Finite sums of elementary component products converge to every joint Schwartz kernel. -/
theorem dense_jointProductSpan {d : ℕ} {I : Type*} [Fintype I]
    (hd : 0 < d) (n : ℕ) : Dense (jointProductSpan d I n : Set (JointTest d I n)) := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let P := jointProductSpan d I n
  let S := SchwartzMap.productSpan (EuclideanSpace ℝ (Fin d)) n
  have hsingle (α : Fin n → I) (f : 𝓢(Fin n → EuclideanSpace ℝ (Fin d), ℂ)) :
      Pi.single α f ∈ P.topologicalClosure := by
    let L := ContinuousLinearMap.single ℂ
      (fun _ : Fin n → I => 𝓢(Fin n → EuclideanSpace ℝ (Fin d), ℂ)) α
    have hmap : S ≤ P.comap L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨fs, rfl⟩
      change Pi.single α (GaussianField.complexProductTensor fs) ∈ P
      rw [← jointProduct_single]
      exact Submodule.subset_span ⟨_, rfl⟩
    have hmap' : Set.MapsTo L (S : Set _) (P : Set _) := hmap
    exact hmap'.closure L.continuous (SchwartzMap.dense_productSpan n f)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro h hh
  have heq : h = ∑ α, Pi.single α (h α) := by ext α x; simp
  rw [heq]
  exact P.topologicalClosure.sum_mem (fun α _ => hsingle α (h α))

/-- The inclusion needed for the bundled extension into L² has dense range. -/
theorem denseRange_jointProductSpan_subtype {d : ℕ} {I : Type*} [Fintype I]
    (hd : 0 < d) (n : ℕ) :
    DenseRange ((jointProductSpan d I n).subtype : jointProductSpan d I n → JointTest d I n) := by
  change Dense (Set.range (Subtype.val : jointProductSpan d I n → JointTest d I n))
  rw [show Set.range (Subtype.val : jointProductSpan d I n → JointTest d I n) =
    (jointProductSpan d I n : Set (JointTest d I n)) from by ext x; simp]
  exact dense_jointProductSpan (I := I) hd n

theorem isUniformInducing_jointProductSpan_subtype (d : ℕ) (I : Type*) [Fintype I]
    (n : ℕ) :
    IsUniformInducing ((jointProductSpan d I n).subtype :
      jointProductSpan d I n → JointTest d I n) :=
  isUniformEmbedding_subtype_val.isUniformInducing

end EuclideanField
