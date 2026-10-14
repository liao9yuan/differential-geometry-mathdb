import Submission.DifferentialGeometry.Topology.SphereSeparation.SphereCellularComparison
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmallChainsPrism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

def topologicalIntersectionToRight
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    TopCat.of (A ∩ B : Set X) ⟶ TopCat.of B :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2.2⟩, by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToRight ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToRight


def topologicalIntersectionToLeft
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    TopCat.of (A ∩ B : Set X) ⟶ TopCat.of A :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2.1⟩, by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToLeft ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalIntersectionToLeft

set_option backward.isDefEq.respectTransparency false in
theorem singularChainsIntersectionToRight_eq_chainMap
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsIntersectionToRight A B =
      integerSingularChainMap (topologicalIntersectionToRight A B) := by
  change singularChainsIntersectionToRight A B =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalIntersectionToRight A B))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsIntersectionToRight,
    singularChainsIntersectionInfIso, singularChainsSubspaceRangeIso,
    topologicalIntersectionToRight]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight_eq_chainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight_eq_chainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight_eq_chainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight_eq_chainMap

set_option backward.isDefEq.respectTransparency false in
theorem singularChainsIntersectionToLeft_eq_chainMap
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsIntersectionToLeft A B =
      integerSingularChainMap (topologicalIntersectionToLeft A B) := by
  change singularChainsIntersectionToLeft A B =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalIntersectionToLeft A B))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsIntersectionToLeft,
    singularChainsIntersectionInfIso, singularChainsSubspaceRangeIso,
    topologicalIntersectionToLeft]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft_eq_chainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft_eq_chainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft_eq_chainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft_eq_chainMap

set_option backward.isDefEq.respectTransparency false in
theorem singularChainsLeftToSmall_comp_inclusion
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsLeftToSmall A B ≫
        smallSingularChainInclusion (TopCat.of X) A B =
      integerSingularChainMap (topologicalSubspaceInclusion A) := by
  change singularChainsLeftToSmall A B ≫
      SSet.chainComplexMap
        (smallSingularSubcomplex (TopCat.of X) A B).ι
        (ModuleCat.of ℤ ℤ) =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubspaceInclusion A))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsLeftToSmall, singularChainsSubspaceRangeIso,
    smallSingularSubcomplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall_comp_inclusion

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem singularChainsRightToSmall_comp_inclusion
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsRightToSmall A B ≫
        smallSingularChainInclusion (TopCat.of X) A B =
      integerSingularChainMap (topologicalSubspaceInclusion B) := by
  change singularChainsRightToSmall A B ≫
      SSet.chainComplexMap
        (smallSingularSubcomplex (TopCat.of X) A B).ι
        (ModuleCat.of ℤ ℤ) =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubspaceInclusion B))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsRightToSmall, singularChainsSubspaceRangeIso,
    smallSingularSubcomplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall_comp_inclusion



def subspaceOutsideHomeomorphInterCompl
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    subspaceOutside A U ≃ₜ (A ∩ Uᶜ : Set X) :=
  subspaceOutsideHomeomorphDiff A U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphInterCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphInterCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphInterCompl ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphInterCompl

def subspaceOutsideToIntersection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    TopCat.of (subspaceOutside A U) ⟶ TopCat.of (A ∩ Uᶜ : Set X) :=
  (TopCat.isoOfHomeo (subspaceOutsideHomeomorphInterCompl A U)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideToIntersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideToIntersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideToIntersection ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideToIntersection

theorem subspaceOutside_intersection_comm
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    topologicalSubspaceInclusion (subspaceOutside A U) ≫
        𝟙 (TopCat.of (Uᶜ : Set X)) =
      subspaceOutsideToIntersection A U ≫
        topologicalIntersectionToRight A Uᶜ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceOutside_intersection_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceOutside_intersection_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceOutside_intersection_comm ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceOutside_intersection_comm

noncomputable def relativeSubspaceOutsideToIntersection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ⟶
      relativeSingularChainComplex
        (topologicalIntersectionToRight A Uᶜ) :=
  relativeSingularChainMap
    (topologicalSubspaceInclusion (subspaceOutside A U))
    (topologicalIntersectionToRight A Uᶜ)
    (subspaceOutsideToIntersection A U)
    (𝟙 (TopCat.of (Uᶜ : Set X)))
    (subspaceOutside_intersection_comm A U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideToIntersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideToIntersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideToIntersection ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideToIntersection

theorem isIso_relativeSubspaceOutsideToIntersection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    IsIso (relativeSubspaceOutsideToIntersection A U) := by
  let _ : _root_.CategoryTheory.IsIso (subspaceOutsideToIntersection A U) := by
    unfold subspaceOutsideToIntersection
    infer_instance
  let _ : _root_.CategoryTheory.IsIso (𝟙 (TopCat.of (Uᶜ : Set X))) := by infer_instance
  exact isIso_relativeSingularChainMap
    (topologicalSubspaceInclusion (subspaceOutside A U))
    (topologicalIntersectionToRight A Uᶜ)
    (subspaceOutsideToIntersection A U)
    (𝟙 (TopCat.of (Uᶜ : Set X)))
    (subspaceOutside_intersection_comm A U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSubspaceOutsideToIntersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSubspaceOutsideToIntersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSubspaceOutsideToIntersection ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSubspaceOutsideToIntersection

noncomputable def relativeSubspaceOutsideIsoMayerVietoris
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ≅
      _root_.CategoryTheory.Limits.cokernel (integerSingularChainMap
        (topologicalIntersectionToRight A Uᶜ)) := by
  let _ := isIso_relativeSubspaceOutsideToIntersection A U
  exact _root_.CategoryTheory.asIso (relativeSubspaceOutsideToIntersection A U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideIsoMayerVietoris then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideIsoMayerVietoris"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideIsoMayerVietoris ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSubspaceOutsideIsoMayerVietoris

@[reassoc]
theorem relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        (relativeSubspaceOutsideIsoMayerVietoris A U).hom =
      integerSingularChainMap (𝟙 (TopCat.of (Uᶜ : Set X))) ≫
        cokernel.π (integerSingularChainMap
          (topologicalIntersectionToRight A Uᶜ)) := by
  change relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        relativeSubspaceOutsideToIntersection A U = _
  exact relativeSingularChainProjection_naturality
    (topologicalSubspaceInclusion (subspaceOutside A U))
    (topologicalIntersectionToRight A Uᶜ)
    (subspaceOutsideToIntersection A U)
    (𝟙 (TopCat.of (Uᶜ : Set X)))
    (subspaceOutside_intersection_comm A U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom

noncomputable def topologicalRelativeUnionComparison
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    _root_.CategoryTheory.Limits.cokernel (integerSingularChainMap
        (topologicalIntersectionToRight A B)) ⟶
      cokernel (singularChainsLeftToSmall A B) :=
  cokernel.map _ _
    (integerSingularChainMap (topologicalIntersectionToLeft A B))
    (singularChainsRightToSmall A B) (by
      rw [← singularChainsIntersectionToRight_eq_chainMap,
        ← singularChainsIntersectionToLeft_eq_chainMap]
      exact (integerSingularChains_isPushout_subspaces A B).w.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison

@[reassoc (attr := simp)]
theorem topologicalRelativeUnionComparison_projection
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel.π (integerSingularChainMap
          (topologicalIntersectionToRight A B)) ≫
        topologicalRelativeUnionComparison A B =
      singularChainsRightToSmall A B ≫
        cokernel.π (singularChainsLeftToSmall A B) := by
  simp [topologicalRelativeUnionComparison]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison_projection ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionComparison_projection


theorem isIso_topologicalRelativeUnionComparison
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    IsIso (topologicalRelativeUnionComparison A B) := by
  have h₀ := integerSingularChains_isPushout_subspaces A B
  rw [singularChainsIntersectionToRight_eq_chainMap,
    singularChainsIntersectionToLeft_eq_chainMap] at h₀
  let h := h₀.flip
  exact _root_.CategoryTheory.Limits.isIso_cokernel_map_of_isPushout h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_topologicalRelativeUnionComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_topologicalRelativeUnionComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_topologicalRelativeUnionComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_topologicalRelativeUnionComparison


noncomputable def topologicalRelativeUnionIso
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    _root_.CategoryTheory.Limits.cokernel (integerSingularChainMap
        (topologicalIntersectionToRight A B)) ≅
      cokernel (singularChainsLeftToSmall A B) := by
  let _ := isIso_topologicalRelativeUnionComparison A B
  exact _root_.CategoryTheory.asIso (topologicalRelativeUnionComparison A B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalRelativeUnionIso

noncomputable def excisionSourceRelativeIsoSmallRelative
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ≅
      cokernel (singularChainsLeftToSmall A Uᶜ) :=
  relativeSubspaceOutsideIsoMayerVietoris A U ≪≫
    topologicalRelativeUnionIso A Uᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative

@[reassoc]
theorem excisionSourceRelativeIsoSmallRelative_projection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        (excisionSourceRelativeIsoSmallRelative A U).hom =
      singularChainsRightToSmall A Uᶜ ≫
        cokernel.π (singularChainsLeftToSmall A Uᶜ) := by
  change relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        (relativeSubspaceOutsideIsoMayerVietoris A U).hom ≫
          (topologicalRelativeUnionIso A Uᶜ).hom = _
  rw [← Category.assoc,
    relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom,
    integerSingularChainMap_id, Category.id_comp]
  change cokernel.π (integerSingularChainMap
        (topologicalIntersectionToRight A Uᶜ)) ≫
      topologicalRelativeUnionComparison A Uᶜ = _
  exact topologicalRelativeUnionComparison_projection A Uᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative_projection ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionSourceRelativeIsoSmallRelative_projection

noncomputable def smallRelativeToFullRelativeChainMap
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    _root_.CategoryTheory.Limits.cokernel (singularChainsLeftToSmall A B) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion A) :=
  cokernel.map
    (singularChainsLeftToSmall A B)
    (integerSingularChainMap (topologicalSubspaceInclusion A))
    (𝟙 (integerSingularChains (TopCat.of A)))
    (smallSingularChainInclusion (TopCat.of X) A B)
    (by simpa using singularChainsLeftToSmall_comp_inclusion A B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap

@[reassoc (attr := simp)]
theorem smallRelativeToFullRelativeChainMap_projection
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel.π (singularChainsLeftToSmall A B) ≫
        smallRelativeToFullRelativeChainMap A B =
      smallSingularChainInclusion (TopCat.of X) A B ≫
        relativeSingularChainProjection (topologicalSubspaceInclusion A) := by
  simp only [smallRelativeToFullRelativeChainMap, cokernel.π_desc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap_projection ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallRelativeToFullRelativeChainMap_projection

theorem quasiIso_smallRelativeToFullRelativeChainMap
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hsmall : QuasiIso
      (smallSingularChainInclusion (TopCat.of X) A B)) :
    QuasiIso (smallRelativeToFullRelativeChainMap A B) := by
  let j := SSet.Subcomplex.homOfLE
    (le_sup_left : singularSubspaceRange (A := A) ≤
      singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B))
  let _ : _root_.CategoryTheory.Mono (SSet.chainComplexMap j (ModuleCat.of ℤ ℤ)) :=
    mono_integerSimplicialChainMap j
  let _ : _root_.CategoryTheory.Mono (singularChainsLeftToSmall A B) := by
    dsimp [singularChainsLeftToSmall]
    infer_instance
  let _ : _root_.CategoryTheory.Mono
      (integerSingularChainMap (topologicalSubspaceInclusion A)) :=
    mono_integerSingularChainMap_subspace A
  apply quasiIso_cokernelMap
    (singularChainsLeftToSmall A B)
    (integerSingularChainMap (topologicalSubspaceInclusion A))
    (𝟙 (integerSingularChains (TopCat.of A)))
    (smallSingularChainInclusion (TopCat.of X) A B)
    (by simpa using singularChainsLeftToSmall_comp_inclusion A B)
  · infer_instance
  · exact hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallRelativeToFullRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallRelativeToFullRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallRelativeToFullRelativeChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallRelativeToFullRelativeChainMap



noncomputable def excisionRelativeSingularChainMapViaSmall
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion A) :=
  (excisionSourceRelativeIsoSmallRelative A U).hom ≫
    smallRelativeToFullRelativeChainMap A Uᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall

set_option backward.isDefEq.respectTransparency false in
theorem excisionRelativeSingularChainMapViaSmall_eq
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    excisionRelativeSingularChainMapViaSmall A U =
      excisionRelativeSingularChainMap A U := by
  apply (_root_.CategoryTheory.cancel_epi (relativeSingularChainProjection
    (topologicalSubspaceInclusion (subspaceOutside A U)))).1
  rw [excisionRelativeSingularChainMapViaSmall,
    excisionSourceRelativeIsoSmallRelative_projection_assoc,
    smallRelativeToFullRelativeChainMap_projection,
    singularChainsRightToSmall_comp_inclusion_assoc]
  simp [excisionRelativeSingularChainMap,
    relativeSingularChainMapOfSubspaces]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMapViaSmall_eq

theorem quasiIso_excisionRelativeSingularChainMap
    {X : Type} [TopologicalSpace X] (A U : Set X)
    (h : closure U ⊆ interior A) :
    QuasiIso (excisionRelativeSingularChainMap A U) := by
  rw [← excisionRelativeSingularChainMapViaSmall_eq A U]
  let _ : QuasiIso
      ((excisionSourceRelativeIsoSmallRelative A U).hom) := by
    infer_instance
  have hsmall : QuasiIso
      (smallSingularChainInclusion (TopCat.of X) A Uᶜ) :=
    quasiIso_smallSingularChainInclusion_of_openCover_refines
      (TopCat.of X)
      (isOpen_excisionCoverNear A)
      (isOpen_excisionCoverFar U)
      (excisionCover_union h)
      (excisionCoverNear_subset A)
      (excisionCoverFar_subset U)
  let _ : QuasiIso (smallRelativeToFullRelativeChainMap A Uᶜ) :=
    quasiIso_smallRelativeToFullRelativeChainMap A Uᶜ hsmall
  change QuasiIso
    ((excisionSourceRelativeIsoSmallRelative A U).hom ≫
      smallRelativeToFullRelativeChainMap A Uᶜ)
  exact inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_excisionRelativeSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_excisionRelativeSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_excisionRelativeSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_excisionRelativeSingularChainMap

theorem singularExcisionFor
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    SingularExcisionFor A U := by
  intro h n
  let _ : QuasiIso (excisionRelativeSingularChainMap A U) :=
    quasiIso_excisionRelativeSingularChainMap A U h
  change _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (excisionRelativeSingularChainMap A U) n)
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularExcisionFor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularExcisionFor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularExcisionFor ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularExcisionFor

end DifferentialGeometry.Topology.SphereSeparation
