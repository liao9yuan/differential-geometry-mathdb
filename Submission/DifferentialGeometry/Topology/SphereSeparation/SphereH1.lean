import Submission.DifferentialGeometry.Topology.SphereSeparation.ContractibleAmbient
import Submission.DifferentialGeometry.Topology.SphereSeparation.CircleComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

theorem isZero_mayerVietorisMiddleHomology_one
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of B) 1)) :
    _root_.CategoryTheory.Limits.IsZero
      ((integerSingularChains_isPushout_subspaces A B).shortComplex.X₂.homology 1) := by
  let H := HomologicalComplex.homologyFunctor
    (ModuleCat ℤ) (ComplexShape.down ℕ) 1
  let : H.Additive := inferInstance
  let : _root_.CategoryTheory.Limits.PreservesFiniteBiproducts H :=
    Functor.preservesFiniteBiproductsOfAdditive H
  let : _root_.CategoryTheory.Limits.PreservesBinaryBiproduct
      (integerSingularChainComplex (TopCat.of A))
      (integerSingularChainComplex (TopCat.of B)) H :=
    _root_.CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBiproduct H _ _
  apply IsZero.of_iso _
    (H.mapBiprod
      (integerSingularChainComplex (TopCat.of A))
      (integerSingularChainComplex (TopCat.of B)))
  exact (_root_.CategoryTheory.Limits.biprod_isZero_iff _ _).2 ⟨hA, hB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_mayerVietorisMiddleHomology_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_mayerVietorisMiddleHomology_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_mayerVietorisMiddleHomology_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_mayerVietorisMiddleHomology_one

theorem mono_homologyMap_intersectionToLeft_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)] :
    _root_.CategoryTheory.Mono (HomologicalComplex.homologyMap
      (singularChainsIntersectionToLeft A B) 0) := by
  rw [singularChainsIntersectionToLeft_eq_chainMap]
  let f := topologicalIntersectionToLeft A B
  let : _root_.CategoryTheory.IsIso ((TopCat.of (A ∩ B : Set X)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) := inferInstance
  let hεmono : _root_.CategoryTheory.Mono ((TopCat.of (A ∩ B : Set X)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) := IsIso.mono_of_iso _
  exact @_root_.CategoryTheory.mono_of_mono_fac _ _ _ _ _ _ _ _ hεmono
    (singularHomologyZeroAugmentation_naturality f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_homologyMap_intersectionToLeft_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_homologyMap_intersectionToLeft_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_homologyMap_intersectionToLeft_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_homologyMap_intersectionToLeft_zero

theorem mono_mayerVietorisIntersectionHomologyMap_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)] :
    _root_.CategoryTheory.Mono (HomologicalComplex.homologyMap
      (integerSingularChains_isPushout_subspaces A B).shortComplex.f 0) := by
  let left := singularChainsIntersectionToLeft A B
  let right := singularChainsIntersectionToRight A B
  change _root_.CategoryTheory.Mono (HomologicalComplex.homologyMap
    (biprod.lift left (-right)) 0)
  let p :
      (integerSingularChains (TopCat.of A) ⊞
          integerSingularChains (TopCat.of B)) ⟶
        integerSingularChains (TopCat.of A) := biprod.fst
  have : _root_.CategoryTheory.Mono (HomologicalComplex.homologyMap left 0) :=
    mono_homologyMap_intersectionToLeft_zero A B
  have hcomp :
      HomologicalComplex.homologyMap
          (biprod.lift left (-right)) 0 ≫
        HomologicalComplex.homologyMap p 0 =
      HomologicalComplex.homologyMap left 0 := by
    rw [← HomologicalComplex.homologyMap_comp]
    rw [biprod.lift_fst]
  have : _root_.CategoryTheory.Mono
      (HomologicalComplex.homologyMap
          (biprod.lift left (-right)) 0 ≫
        HomologicalComplex.homologyMap p 0) := by
    rw [hcomp]
    infer_instance
  exact _root_.CategoryTheory.mono_of_mono_fac hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_mayerVietorisIntersectionHomologyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_mayerVietorisIntersectionHomologyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_mayerVietorisIntersectionHomologyMap_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_mayerVietorisIntersectionHomologyMap_zero

noncomputable def singularMayerVietorisBoundaryOneZero
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (smallSingularChainComplex (TopCat.of X) A B).homology 1 ⟶
      (integerSingularChainComplex (TopCat.of (A ∩ B : Set X))).homology 0 :=
  (integerSingularChains_mayerVietoris_shortExact_subspaces A B).δ
    1 0 (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero

theorem mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of B) 1)) :
    Mono (singularMayerVietorisBoundaryOneZero A B) := by
  let hS := integerSingularChains_mayerVietoris_shortExact_subspaces A B
  apply (hS.homology_exact₃ 1 0 (by simp)).mono_g
  exact (isZero_mayerVietorisMiddleHomology_one A B hA hB).eq_of_src _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing

@[reassoc]
theorem singularMayerVietorisBoundaryOneZero_comp
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularMayerVietorisBoundaryOneZero A B ≫
        HomologicalComplex.homologyMap
          (integerSingularChains_isPushout_subspaces A B).shortComplex.f 0 = 0 := by
  exact (integerSingularChains_mayerVietoris_shortExact_subspaces A B).δ_comp
    1 0 (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_comp ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_comp

theorem singularMayerVietorisBoundaryOneZero_eq_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)] :
    singularMayerVietorisBoundaryOneZero A B = 0 := by
  exact
    ((integerSingularChains_mayerVietoris_shortExact_subspaces A B
      ).homology_exact₁ 1 0 (by simp)).mono_g_iff.mp
        (mono_mayerVietorisIntersectionHomologyMap_zero A B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_eq_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularMayerVietorisBoundaryOneZero_eq_zero

theorem isZero_smallSingularHomology_one_of_memberVanishing
    (X : TopCat) (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)]
    (hA : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of B) 1)) :
    IsZero ((smallSingularChainComplex X A B).homology 1) := by
  let δ := singularMayerVietorisBoundaryOneZero A B
  have : _root_.CategoryTheory.Mono δ :=
    mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing A B hA hB
  have hδzero : δ = 0 :=
    singularMayerVietorisBoundaryOneZero_eq_zero A B
  rw [IsZero.iff_id_eq_zero]
  apply (_root_.CategoryTheory.cancel_mono δ).1
  simp [hδzero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_smallSingularHomology_one_of_memberVanishing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_smallSingularHomology_one_of_memberVanishing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_smallSingularHomology_one_of_memberVanishing ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_smallSingularHomology_one_of_memberVanishing

theorem isZero_integerSingularHomology_one_of_openCover
    (X : TopCat) (A B : Set X)
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hcover : A ∪ B = Set.univ)
    [PathConnectedSpace (A ∩ B : Set X)]
    (hA : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of B) 1)) :
    IsZero (integerSingularHomology X 1) := by
  have hsmall : _root_.CategoryTheory.Limits.IsZero ((smallSingularChainComplex X A B).homology 1) :=
    isZero_smallSingularHomology_one_of_memberVanishing X A B hA hB
  have hq : QuasiIso (smallSingularChainInclusion X A B) :=
    quasiIso_smallSingularChainInclusion X A B hAopen hBopen hcover
  let : QuasiIso (smallSingularChainInclusion X A B) := hq
  let : _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (smallSingularChainInclusion X A B) 1) := inferInstance
  exact IsZero.of_iso hsmall
    (_root_.CategoryTheory.asIso (HomologicalComplex.homologyMap
      (smallSingularChainInclusion X A B) 1)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_openCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_openCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_openCover ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_openCover




noncomputable def sphereTwoNorthPoint : SphereTwo :=
  ⟨EuclideanSpace.single 0 1, by simp [SphereTwo]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint


noncomputable def sphereTwoSouthPoint : SphereTwo :=
  ⟨EuclideanSpace.single 0 (-1), by simp [SphereTwo]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoSouthPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoSouthPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoSouthPoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoSouthPoint


theorem sphereTwoNorthPoint_ne_southPoint :
    sphereTwoNorthPoint ≠ sphereTwoSouthPoint := by
  intro h
  have hcoord := congrArg (fun x : SphereTwo ↦ x.1 0) h
  norm_num [sphereTwoNorthPoint, sphereTwoSouthPoint] at hcoord

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint_ne_southPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint_ne_southPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint_ne_southPoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoNorthPoint_ne_southPoint

theorem sphereTwoPunctureIntersection_pathConnectedSpace
    (p q : SphereTwo) (hpq : p ≠ q) :
    PathConnectedSpace
      (({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ : Set SphereTwo) := by
  let qp : ({p}ᶜ : Set SphereTwo) := ⟨q, by simp [hpq.symm]⟩
  let e := sphereTwoPunctureHomeomorph p
  let a : EuclideanPlane := e qp
  let er : ({qp}ᶜ : Set ({p}ᶜ : Set SphereTwo)) ≃ₜ
      ({a}ᶜ : Set EuclideanPlane) :=
    e.subtype (by
      intro x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hx h
        exact hx (e.injective h)
      · intro hx h
        exact hx (congrArg e h))
  let E : (({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ : Set SphereTwo) ≃ₜ
      ({a}ᶜ : Set EuclideanPlane) :=
    (Homeomorph.setCongr (sphereTwoPuncture_inter p q)).trans
      ((twoPointComplHomeomorphNestedCompl p q hpq).trans er)
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    rw [← Module.finrank_eq_rank']
    norm_num [EuclideanPlane, Module.finrank_fin_fun]
  let : PathConnectedSpace ({a}ᶜ : Set EuclideanPlane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank a)
  exact E.symm.surjective.pathConnectedSpace E.symm.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureIntersection_pathConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureIntersection_pathConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureIntersection_pathConnectedSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureIntersection_pathConnectedSpace

theorem isZero_integerSingularHomology_sphereTwo_one :
    IsZero (integerSingularHomology (TopCat.of SphereTwo) 1) := by
  let p := sphereTwoNorthPoint
  let q := sphereTwoSouthPoint
  have hpq : p ≠ q := sphereTwoNorthPoint_ne_southPoint
  let : ContractibleSpace ({p}ᶜ : Set SphereTwo) :=
    sphereTwoPuncture_contractible p
  let : ContractibleSpace ({q}ᶜ : Set SphereTwo) :=
    sphereTwoPuncture_contractible q
  let : PathConnectedSpace
      (({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ : Set SphereTwo) :=
    sphereTwoPunctureIntersection_pathConnectedSpace p q hpq
  exact isZero_integerSingularHomology_one_of_openCover
    (TopCat.of SphereTwo) ({p}ᶜ : Set SphereTwo) {q}ᶜ
    (isOpen_sphereTwoPuncture p) (isOpen_sphereTwoPuncture q)
    (sphereTwoPunctureCover hpq)
    (isZero_integerSingularHomology_one_of_contractible _)
    (isZero_integerSingularHomology_one_of_contractible _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one

end DifferentialGeometry.Topology.SphereSeparation
