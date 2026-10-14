import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.DifferentialGeometry.Topology.SphereSeparation.GlobalNormal
import Submission.DifferentialGeometry.Topology.SphereSeparation.ManifoldInverseFunction
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Analysis.Normed.Operator.Banach

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation


def normalFieldParametrization
    (e ν : SphereTwo → EuclideanThree) : SphereTwo × ℝ → EuclideanThree :=
  fun z ↦ e z.1 + z.2 • ν z.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization ``Submission.DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization

@[simp]
theorem normalFieldParametrization_zero
    (e ν : SphereTwo → EuclideanThree) (p : SphereTwo) :
    normalFieldParametrization e ν (p, 0) = e p := by
  simp [normalFieldParametrization]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrization_zero


def normalZeroSection : Set (SphereTwo × ℝ) :=
  Set.range fun p : SphereTwo ↦ (p, (0 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.normalZeroSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.normalZeroSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.normalZeroSection ``Submission.DifferentialGeometry.Topology.SphereSeparation.normalZeroSection


theorem isCompact_normalZeroSection : IsCompact normalZeroSection := by
  rw [normalZeroSection, ← Set.image_univ]
  exact isCompact_univ.image (continuous_id.prodMk continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isCompact_normalZeroSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isCompact_normalZeroSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isCompact_normalZeroSection ``Submission.DifferentialGeometry.Topology.SphereSeparation.isCompact_normalZeroSection

theorem exists_uniform_axial_interval_subset
    {U : Set (SphereTwo × ℝ)} (hU : IsOpen U)
    (hzero : normalZeroSection ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ Set.univ ×ˢ _root_.Set.Ioo (-a) a ⊆ U := by
  have hprod : (Set.univ : Set SphereTwo) ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨p, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := by simpa using ht
    subst t
    exact hzero ⟨p, rfl⟩
  obtain ⟨u, v, hu, hv, huniv, hzero_v, huv⟩ :=
    generalized_tube_lemma (s := (Set.univ : Set SphereTwo))
      isCompact_univ (t := ({0} : Set ℝ)) isCompact_singleton hU hprod
  have hv_nhds : v ∈ 𝓝 (0 : ℝ) :=
    hv.mem_nhds (hzero_v (by simp))
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hv_nhds
  refine ⟨a, ha, ?_⟩
  intro z hz
  apply huv
  refine ⟨huniv (by simp), hball ?_⟩
  simpa [Real.ball_zero_eq_Ioo] using hz.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_axial_interval_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_uniform_axial_interval_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_axial_interval_subset ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_uniform_axial_interval_subset

theorem contMDiff_normalFieldParametrization
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν) :
    ContMDiff
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (normalFieldParametrization e ν) := by
  exact (he.contMDiff.comp contMDiff_fst).add
    ((contMDiff_snd.smul (hν.comp contMDiff_fst)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.contMDiff_normalFieldParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.contMDiff_normalFieldParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.contMDiff_normalFieldParametrization ``Submission.DifferentialGeometry.Topology.SphereSeparation.contMDiff_normalFieldParametrization

theorem mvfderiv_normalFieldParametrization_zero_apply
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (p : SphereTwo)
    (v : TangentSpace
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ ℝ)) (p, 0)) :
    NormedSpace.fromTangentSpace (normalFieldParametrization e ν (p, 0))
      (mfderiv
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ EuclideanThree)
        (normalFieldParametrization e ν) (p, 0) v) =
        mvfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) e p v.1 +
          v.2 • ν p := by
  have hF : MDifferentiableAt
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ EuclideanThree)
      (normalFieldParametrization e ν) (p, 0) :=
    (contMDiff_normalFieldParametrization he hν (p, 0)).mdifferentiableAt
      (by simp)
  have hfirst :
      NormedSpace.fromTangentSpace (normalFieldParametrization e ν (p, 0))
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ EuclideanThree)
          (fun z : SphereTwo ↦ normalFieldParametrization e ν (z, 0)) p v.1) =
        mvfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) e p v.1 := by
    rw [show (fun z : SphereTwo ↦ normalFieldParametrization e ν (z, 0)) = e by
      funext z
      simp [normalFieldParametrization]]
    rw [normalFieldParametrization_zero]
    rfl
  have hsecond :
      NormedSpace.fromTangentSpace (normalFieldParametrization e ν (p, 0))
        (mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ EuclideanThree)
          (fun y : ℝ ↦ normalFieldParametrization e ν (p, y)) 0 v.2) =
        v.2 • ν p := by
    rw [mfderiv_eq_fderiv]
    have hd := ((hasFDerivAt_const (x := (0 : ℝ)) (c := e p)).add
      ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (ν p))).fderiv
    have hd' : fderiv ℝ (fun y : ℝ ↦ e p + y • ν p) 0 =
        0 + (ContinuousLinearMap.id ℝ ℝ).smulRight (ν p) := by
      convert hd using 1
      ext y
      simp
    rw [show (fun y : ℝ ↦ normalFieldParametrization e ν (p, y)) =
        (fun y : ℝ ↦ e p + y • ν p) by rfl]
    rw [hd']
    rw [zero_add]
    rw [normalFieldParametrization_zero]
    rfl
  rw [mfderiv_prod_eq_add_apply hF, map_add, hfirst, hsecond]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mvfderiv_normalFieldParametrization_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mvfderiv_normalFieldParametrization_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mvfderiv_normalFieldParametrization_zero_apply ``Submission.DifferentialGeometry.Topology.SphereSeparation.mvfderiv_normalFieldParametrization_zero_apply

theorem injective_mfderiv_normalFieldParametrization_zero
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0)
    (p : SphereTwo) :
    Function.Injective
      (mfderiv
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ EuclideanThree)
        (normalFieldParametrization e ν) (p, (0 : ℝ))) := by
  intro v w hvw
  have hvw' := congrArg
    (NormedSpace.fromTangentSpace
      (normalFieldParametrization e ν (p, 0))) hvw
  rw [mvfderiv_normalFieldParametrization_zero_apply he hν p v,
    mvfderiv_normalFieldParametrization_zero_apply he hν p w] at hvw'
  let A := mvfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) e p
  let v₁ : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) p := v.1
  let w₁ : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) p := w.1
  let v₂ : ℝ := v.2
  let w₂ : ℝ := w.2
  have hvw_components : A v₁ + v₂ • ν p = A w₁ + w₂ • ν p := by
    simpa [A, v₁, w₁, v₂, w₂] using hvw'
  have hcommon : A (v₁ - w₁) = (w₂ - v₂) • ν p := by
    rw [map_sub, sub_smul]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa [add_comm] using hvw_components
  have htangent : A (v₁ - w₁) ∈ embeddedSphereTangentPlane e p := by
    exact ⟨v₁ - w₁, rfl⟩
  have hnormal : A (v₁ - w₁) ∈ embeddedSphereNormalLine e p := by
    rw [hcommon]
    exact Submodule.smul_mem _ _ (hνnormal p)
  have hcommon_zero : A (v₁ - w₁) = 0 := by
    have hb : A (v₁ - w₁) ∈ (⊥ : Submodule ℝ EuclideanThree) :=
      (isCompl_embeddedSphereTangentPlane_normalLine e p).disjoint.le_bot
        ⟨htangent, hnormal⟩
    simpa using hb
  have hAinj : Function.Injective A :=
    injective_mvfderiv_of_isImmersionAtOfComplement_real
      (isImmersionAtOfComplement_real_of_isSmoothEmbedding he p)
  have hfst : v₁ = w₁ := by
    apply sub_eq_zero.mp
    apply hAinj
    rw [map_zero]
    exact hcommon_zero
  have hsnd : v₂ = w₂ := by
    apply smul_left_injective ℝ (hνne p)
    simpa [hfst] using hvw_components
  apply Prod.ext
  · change v₁ = w₁
    exact hfst
  · change v₂ = w₂
    exact hsnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.injective_mfderiv_normalFieldParametrization_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.injective_mfderiv_normalFieldParametrization_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.injective_mfderiv_normalFieldParametrization_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.injective_mfderiv_normalFieldParametrization_zero

theorem bijective_mfderiv_normalFieldParametrization_zero
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0)
    (p : SphereTwo) :
    Function.Bijective
      (mfderiv
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ EuclideanThree)
        (normalFieldParametrization e ν) (p, 0)) := by
  let L := mfderiv
    ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
      (modelWithCornersSelf ℝ ℝ))
    (modelWithCornersSelf ℝ EuclideanThree)
    (normalFieldParametrization e ν) (p, (0 : ℝ))
  have hinj : Function.Injective L :=
    injective_mfderiv_normalFieldParametrization_zero
      he hν hνnormal hνne p
  let finiteSource : FiniteDimensional ℝ
      (TangentSpace
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ)) (p, (0 : ℝ))) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
    infer_instance
  let finiteTarget : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersSelf ℝ EuclideanThree)
        (normalFieldParametrization e ν (p, (0 : ℝ)))) := by
    change FiniteDimensional ℝ EuclideanThree
    infer_instance
  have hdim : Module.finrank ℝ
      (TangentSpace
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ)) (p, (0 : ℝ))) =
      Module.finrank ℝ
        (TangentSpace (modelWithCornersSelf ℝ EuclideanThree)
          (normalFieldParametrization e ν (p, (0 : ℝ)))) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ EuclideanThree
    norm_num [EuclideanThree, Module.finrank_fin_fun]
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bijective_mfderiv_normalFieldParametrization_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bijective_mfderiv_normalFieldParametrization_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bijective_mfderiv_normalFieldParametrization_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.bijective_mfderiv_normalFieldParametrization_zero

noncomputable def normalFieldParametrizationDifferentialLinearEquiv
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0)
    (p : SphereTwo) :
    TangentSpace
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ)) (p, (0 : ℝ)) ≃ₗ[ℝ]
      TangentSpace (modelWithCornersSelf ℝ EuclideanThree)
        (normalFieldParametrization e ν (p, (0 : ℝ))) := by
  let L := mfderiv
    ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
      (modelWithCornersSelf ℝ ℝ))
    (modelWithCornersSelf ℝ EuclideanThree)
    (normalFieldParametrization e ν) (p, (0 : ℝ))
  exact LinearEquiv.ofBijective L.toLinearMap
    (bijective_mfderiv_normalFieldParametrization_zero
      he hν hνnormal hνne p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrizationDifferentialLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrizationDifferentialLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrizationDifferentialLinearEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.normalFieldParametrizationDifferentialLinearEquiv

theorem isOpenEmbedding_normalFieldParametrization_restrict
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    {S : Set (SphereTwo × ℝ)} (hS : IsOpen S)
    (hinj : Set.InjOn (normalFieldParametrization e ν) S)
    (hlocal : IsLocalDiffeomorphOn
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (normalFieldParametrization e ν) S) :
    Topology.IsOpenEmbedding
      (fun z : S ↦ normalFieldParametrization e ν z.1) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (contMDiff_normalFieldParametrization he hν).continuous.comp
      continuous_subtype_val
  · intro x y hxy
    exact Subtype.ext (hinj x.2 y.2 hxy)
  · intro O hO
    rw [show (fun z : S ↦ normalFieldParametrization e ν z.1) '' O =
        normalFieldParametrization e ν '' (Subtype.val '' O) by
      ext y
      simp]
    have hOambient : IsOpen (Subtype.val '' O) :=
      hS.isOpenMap_subtype_val O hO
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨x, hxO, rfl⟩
    rcases hxO with ⟨z, hzO, rfl⟩
    obtain ⟨Φ, hzΦ, heq⟩ := hlocal ⟨z.1, z.2⟩
    let A : Set (SphereTwo × ℝ) := (Subtype.val '' O) ∩ Φ.source
    refine ⟨Φ '' A, ?_, ?_, ?_⟩
    · rintro q ⟨r, hr, rfl⟩
      exact ⟨r, hr.1, heq hr.2⟩
    · exact Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hOambient.inter Φ.open_source) _root_.Set.inter_subset_right
    · exact ⟨z.1, ⟨⟨z, hzO, rfl⟩, hzΦ⟩, (heq hzΦ).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict

theorem isOpenEmbedding_normalFieldParametrization_restrict_of_local
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    {S : Set (SphereTwo × ℝ)} (hS : IsOpen S)
    (hinj : Set.InjOn (normalFieldParametrization e ν) S)
    (hlocal : ∀ x ∈ S, ∃ U : Set (SphereTwo × ℝ),
      IsOpen U ∧ x ∈ U ∧
        Topology.IsOpenEmbedding
          (U.domRestrict (normalFieldParametrization e ν))) :
    Topology.IsOpenEmbedding
      (fun z : S ↦ normalFieldParametrization e ν z.1) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (contMDiff_normalFieldParametrization he hν).continuous.comp
      continuous_subtype_val
  · intro x y hxy
    exact Subtype.ext (hinj x.2 y.2 hxy)
  · intro O hO
    rw [show (fun z : S ↦ normalFieldParametrization e ν z.1) '' O =
        normalFieldParametrization e ν '' (Subtype.val '' O) by
      ext y
      simp]
    have hOambient : IsOpen (Subtype.val '' O) :=
      hS.isOpenMap_subtype_val O hO
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨x, hxO, rfl⟩
    have hxS : x ∈ S := by
      rcases hxO with ⟨z, -, rfl⟩
      exact z.2
    obtain ⟨U, hUopen, hxU, hUemb⟩ := hlocal x hxS
    let A : Set U := Subtype.val ⁻¹' (Subtype.val '' O)
    have hAopen : IsOpen A := hOambient.preimage continuous_subtype_val
    refine ⟨U.domRestrict (normalFieldParametrization e ν) '' A, ?_, ?_, ?_⟩
    · rintro q ⟨z, hzA, rfl⟩
      exact ⟨z.1, hzA, rfl⟩
    · exact hUemb.isOpenMap A hAopen
    · exact ⟨⟨x, hxU⟩, hxO, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict_of_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict_of_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict_of_local ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpenEmbedding_normalFieldParametrization_restrict_of_local

theorem exists_uniform_injective_normal_strip
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hlocal : ∀ p : SphereTwo,
      ∃ U ∈ 𝓝 (p, (0 : ℝ)),
        Set.InjOn (normalFieldParametrization e ν) U) :
    ∃ a : ℝ, 0 < a ∧
      Set.InjOn (normalFieldParametrization e ν)
        (Set.univ ×ˢ _root_.Set.Ioo (-a) a) := by
  have hzero_inj : Set.InjOn (normalFieldParametrization e ν)
      normalZeroSection := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    apply Prod.ext
    · exact he.isEmbedding.injective (by simpa using hpq)
    · rfl
  have hFcont : Continuous (normalFieldParametrization e ν) :=
    (contMDiff_normalFieldParametrization he hν).continuous
  obtain ⟨U, hUopen, hzeroU, hUinj⟩ :=
    hzero_inj.exists_isOpen_superset isCompact_normalZeroSection
      (fun _ _ ↦ hFcont.continuousAt) (by
        rintro _ ⟨p, rfl⟩
        exact hlocal p)
  obtain ⟨a, ha, hstripU⟩ :=
    exists_uniform_axial_interval_subset hUopen hzeroU
  exact ⟨a, ha, hUinj.mono hstripU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip

theorem exists_uniform_injective_normal_strip_of_normalField
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      Set.InjOn (normalFieldParametrization e ν)
        (Set.univ ×ˢ _root_.Set.Ioo (-a) a) := by
  apply exists_uniform_injective_normal_strip he hν
  intro p
  exact exists_nhds_injOn_of_contMDiffAt_of_bijective_mfderiv
    ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
      (modelWithCornersSelf ℝ ℝ))
    (modelWithCornersSelf ℝ EuclideanThree) (by simp)
    (contMDiff_normalFieldParametrization he hν).contMDiffAt
    (bijective_mfderiv_normalFieldParametrization_zero
      he hν hνnormal hνne p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip_of_normalField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip_of_normalField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip_of_normalField ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_uniform_injective_normal_strip_of_normalField

theorem exists_uniform_normal_bicollar_of_localDiffeomorphAt_zero
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hlocalzero : ∀ p : SphereTwo,
      IsLocalDiffeomorphAt
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ EuclideanThree) ∞
        (normalFieldParametrization e ν) (p, (0 : ℝ))) :
    ∃ a : ℝ, 0 < a ∧
      Topology.IsOpenEmbedding
        (fun z : (Set.univ ×ˢ _root_.Set.Ioo (-a) a : Set (SphereTwo × ℝ)) ↦
          normalFieldParametrization e ν z.1) := by
  choose Φ hΦmem hΦeq using hlocalzero
  let V : Set (SphereTwo × ℝ) := ⋃ p : SphereTwo, (Φ p).source
  have hVopen : IsOpen V := by
    exact isOpen_iUnion fun p ↦ (Φ p).open_source
  have hzeroV : normalZeroSection ⊆ V := by
    rintro _ ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, hΦmem p⟩
  have hlocalV : IsLocalDiffeomorphOn
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (normalFieldParametrization e ν) V := by
    rintro ⟨x, hxV⟩
    rcases mem_iUnion.mp hxV with ⟨p, hxp⟩
    exact ⟨Φ p, hxp, hΦeq p⟩
  have hzero_inj : Set.InjOn (normalFieldParametrization e ν)
      normalZeroSection := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    apply Prod.ext
    · exact he.isEmbedding.injective (by simpa using hpq)
    · rfl
  have hFcont : Continuous (normalFieldParametrization e ν) :=
    (contMDiff_normalFieldParametrization he hν).continuous
  have hlocalinj : ∀ x ∈ normalZeroSection,
      ∃ U ∈ 𝓝 x, Set.InjOn (normalFieldParametrization e ν) U := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(Φ p).source, (Φ p).open_source.mem_nhds (hΦmem p), ?_⟩
    intro x hx y hy hxy
    apply (Φ p).toOpenPartialHomeomorph.injOn hx hy
    change (Φ p).toPartialEquiv x = (Φ p).toPartialEquiv y
    exact (hΦeq p hx).symm.trans (hxy.trans (hΦeq p hy))
  obtain ⟨U, hUopen, hzeroU, hUinj⟩ :=
    hzero_inj.exists_isOpen_superset isCompact_normalZeroSection
      (fun _ _ ↦ hFcont.continuousAt) hlocalinj
  have hzeroUV : normalZeroSection ⊆ U ∩ V :=
    fun _ hx ↦ ⟨hzeroU hx, hzeroV hx⟩
  obtain ⟨a, ha, hstrip⟩ :=
    exists_uniform_axial_interval_subset (hUopen.inter hVopen) hzeroUV
  let S : Set (SphereTwo × ℝ) := Set.univ ×ˢ _root_.Set.Ioo (-a) a
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hSU : S ⊆ U := fun x hx ↦ (hstrip hx).1
  have hSV : S ⊆ V := fun x hx ↦ (hstrip hx).2
  refine ⟨a, ha, ?_⟩
  change Topology.IsOpenEmbedding
    (fun z : S ↦ normalFieldParametrization e ν z.1)
  exact isOpenEmbedding_normalFieldParametrization_restrict he hν hSopen
    (hUinj.mono hSU) (fun x ↦ hlocalV ⟨x.1, hSV x.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_of_localDiffeomorphAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_of_localDiffeomorphAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_of_localDiffeomorphAt_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_of_localDiffeomorphAt_zero

theorem exists_uniform_normal_bicollar
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      Topology.IsOpenEmbedding
        (fun z : (Set.univ ×ˢ _root_.Set.Ioo (-a) a : Set (SphereTwo × ℝ)) ↦
          normalFieldParametrization e ν z.1) := by
  have hpoint : ∀ p : SphereTwo,
      ∃ U ∈ 𝓝 (p, (0 : ℝ)), IsOpen U ∧
        Topology.IsOpenEmbedding
          (U.domRestrict (normalFieldParametrization e ν)) := by
    intro p
    exact
      exists_nhds_isOpenEmbedding_domRestrict_of_contMDiffAt_of_bijective_mfderiv
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ EuclideanThree) (by simp)
        (contMDiff_normalFieldParametrization he hν).contMDiffAt
        (bijective_mfderiv_normalFieldParametrization_zero
          he hν hνnormal hνne p)
  choose U hUnhds hUopen hUemb using hpoint
  let V : Set (SphereTwo × ℝ) := ⋃ p : SphereTwo, U p
  have hVopen : IsOpen V := isOpen_iUnion hUopen
  have hzeroV : normalZeroSection ⊆ V := by
    rintro _ ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, mem_of_mem_nhds (hUnhds p)⟩
  have hlocalV : ∀ x ∈ V, ∃ W : Set (SphereTwo × ℝ),
      IsOpen W ∧ x ∈ W ∧
        Topology.IsOpenEmbedding
          (W.domRestrict (normalFieldParametrization e ν)) := by
    intro x hxV
    rcases mem_iUnion.mp hxV with ⟨p, hxp⟩
    exact ⟨U p, hUopen p, hxp, hUemb p⟩
  have hzero_inj : Set.InjOn (normalFieldParametrization e ν)
      normalZeroSection := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    apply Prod.ext
    · exact he.isEmbedding.injective (by simpa using hpq)
    · rfl
  have hFcont : Continuous (normalFieldParametrization e ν) :=
    (contMDiff_normalFieldParametrization he hν).continuous
  have hlocalinj : ∀ x ∈ normalZeroSection,
      ∃ W ∈ 𝓝 x, Set.InjOn (normalFieldParametrization e ν) W := by
    rintro _ ⟨p, rfl⟩
    exact ⟨U p, hUnhds p,
      Set.injOn_iff_injective.mpr (hUemb p).injective⟩
  obtain ⟨G, hGopen, hzeroG, hGinj⟩ :=
    hzero_inj.exists_isOpen_superset isCompact_normalZeroSection
      (fun _ _ ↦ hFcont.continuousAt) hlocalinj
  have hzeroGV : normalZeroSection ⊆ G ∩ V :=
    fun _ hx ↦ ⟨hzeroG hx, hzeroV hx⟩
  obtain ⟨a, ha, hstrip⟩ :=
    exists_uniform_axial_interval_subset (hGopen.inter hVopen) hzeroGV
  let S : Set (SphereTwo × ℝ) := Set.univ ×ˢ _root_.Set.Ioo (-a) a
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hSG : S ⊆ G := fun x hx ↦ (hstrip hx).1
  have hSV : S ⊆ V := fun x hx ↦ (hstrip hx).2
  refine ⟨a, ha, ?_⟩
  change Topology.IsOpenEmbedding
    (fun z : S ↦ normalFieldParametrization e ν z.1)
  exact isOpenEmbedding_normalFieldParametrization_restrict_of_local
    he hν hSopen (hGinj.mono hSG) (fun x hx ↦ hlocalV x (hSV hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar

theorem exists_uniform_normal_bicollar_product
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      Topology.IsOpenEmbedding
        (fun z : SphereTwo × (_root_.Set.Ioo (-a) a : Set ℝ) ↦
          e z.1 + z.2.1 • ν z.1) := by
  obtain ⟨a, ha, hcollar⟩ :=
    exists_uniform_normal_bicollar he hν hνnormal hνne
  let domainEquiv :
      SphereTwo × (_root_.Set.Ioo (-a) a : Set ℝ) ≃ₜ
        (Set.univ ×ˢ _root_.Set.Ioo (-a) a : Set (SphereTwo × ℝ)) :=
    (((Homeomorph.Set.univ SphereTwo).symm.prodCongr
      (Homeomorph.refl (_root_.Set.Ioo (-a) a : Set ℝ))).trans
        (Homeomorph.Set.prod (Set.univ : Set SphereTwo) (_root_.Set.Ioo (-a) a)).symm)
  refine ⟨a, ha, ?_⟩
  have hcomp := hcollar.comp domainEquiv.isOpenEmbedding
  simpa [domainEquiv, normalFieldParametrization, Function.comp_def] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_product ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_uniform_normal_bicollar_product

theorem exists_partialDiffeomorph_normalFieldParametrization
    {e ν : SphereTwo → EuclideanThree} (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hν : ContMDiff (𝓡 2) (𝓡 3) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p) (hνne : ∀ p, ν p ≠ 0) :
    ∃ Φ : _root_.PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3)
        (SphereTwo × ℝ) EuclideanThree ∞,
      normalZeroSection ⊆ Φ.source ∧ Φ.toFun = normalFieldParametrization e ν := by
  have hF := contMDiff_normalFieldParametrization he hν
  have hlocal : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞
      (normalFieldParametrization e ν) normalZeroSection := by
    rintro ⟨_, p, rfl⟩
    let T : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanThree :=
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) (normalFieldParametrization e ν) (p, 0)
    have hbij := bijective_mfderiv_normalFieldParametrization_zero he hν hνnormal hνne p
    let A := ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
    apply Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
      (normalFieldParametrization e ν) hF (p, 0) A
    convert! (hF.mdifferentiable (by simp) (p, 0)).hasMFDerivAt using 1
  have hinj : _root_.Set.InjOn (normalFieldParametrization e ν) normalZeroSection := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    exact Prod.ext (he.isEmbedding.injective (by simpa using hpq)) rfl
  let p : SphereTwo := ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm]
    simp⟩
  exact DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hlocal isCompact_normalZeroSection ⟨(p, 0), _root_.Set.mem_range_self _⟩ hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_partialDiffeomorph_normalFieldParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_partialDiffeomorph_normalFieldParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_partialDiffeomorph_normalFieldParametrization ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_partialDiffeomorph_normalFieldParametrization

end DifferentialGeometry.Topology.SphereSeparation
