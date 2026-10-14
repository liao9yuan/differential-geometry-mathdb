import Submission.DifferentialGeometry.Topology.SphereSeparation.TopologicalRelativeUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem singularHomologyZeroAugmentation_naturality
    {X Y : TopCat} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap (integerSingularChainMap f) 0 ≫
        Y.singularHomology₀ε (ModuleCat.of ℤ ℤ) =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
  let K := integerSingularChainComplex X
  let L := integerSingularChainComplex Y
  apply (_root_.CategoryTheory.cancel_epi (K.homologyπ 0)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  apply (_root_.CategoryTheory.cancel_epi K.cycles₀Iso.inv).1
  apply Sigma.hom_ext
  intro x
  let SX := TopCat.toSSet.obj X
  have hlift :
      SX.ιChainComplex x ≫ K.cycles₀Iso.inv =
        K.liftCycles (SX.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (_root_.CategoryTheory.cancel_mono (K.iCycles 0)).1
    rw [HomologicalComplex.liftCycles_i]
    change SX.ιChainComplex x ≫
      (K.cycles₀Iso.inv ≫ K.cycles₀Iso.hom) = SX.ιChainComplex x
    rw [K.cycles₀Iso.inv_hom_id]
    exact Category.comp_id _
  change SX.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
      HomologicalComplex.cyclesMap (integerSingularChainMap f) 0 ≫
        L.homologyπ 0 ≫ Y.singularHomology₀ε (ModuleCat.of ℤ ℤ) =
    SX.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
      K.homologyπ 0 ≫ X.singularHomology₀ε (ModuleCat.of ℤ ℤ)
  rw [← Category.assoc, hlift,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  calc
    _ = 𝟙 (ModuleCat.of ℤ ℤ) := by
      change HomologicalComplex.liftCycles
          ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ))
          ((TopCat.toSSet.obj X).ιChainComplex x ≫
            (SSet.chainComplexMap (TopCat.toSSet.map f)
              (ModuleCat.of ℤ ℤ)).f 0)
          0 (by simp) (by simp) ≫
        HomologicalComplex.homologyπ
            ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)) 0 ≫
          (TopCat.toSSet.obj Y).homology₀ε (ModuleCat.of ℤ ℤ) =
        𝟙 (ModuleCat.of ℤ ℤ)
      simpa only [SSet.ι_chainComplexMap_f] using
        SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
          (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ x)
    _ = SX.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
          K.homologyπ 0 ≫ X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
      rw [← Category.assoc, hlift]
      symm
      exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
        (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularHomologyZeroAugmentation_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularHomologyZeroAugmentation_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularHomologyZeroAugmentation_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularHomologyZeroAugmentation_naturality

@[reassoc]
theorem subspaceSingularHomologyMap_comp_augmentation
    {X : Type} [TopologicalSpace X] (A : Set X) :
    subspaceSingularHomologyMap A 0 ≫
        (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ) =
      (TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ) :=
  singularHomologyZeroAugmentation_naturality
    (topologicalSubspaceInclusion A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap_comp_augmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap_comp_augmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap_comp_augmentation ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap_comp_augmentation

noncomputable def reducedSingularH0IsoKernelSubspaceMap
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X) :
    reducedSingularH0 (TopCat.of A) ≅
      kernel (subspaceSingularHomologyMap A 0) :=
  kernel.mapIso
    (f := (TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ))
    (f' := subspaceSingularHomologyMap A 0)
    (p := Iso.refl _)
    (q := (_root_.CategoryTheory.asIso ((TopCat.of X).singularHomology₀ε
      (ModuleCat.of ℤ ℤ))).symm)
    (by
      apply (_root_.CategoryTheory.cancel_mono ((TopCat.of X).singularHomology₀ε
        (ModuleCat.of ℤ ℤ))).1
      change (((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ) ≫
          _root_.CategoryTheory.inv ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))) ≫
            (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)) =
        ((𝟙 _ ≫ subspaceSingularHomologyMap A 0) ≫
          (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp, subspaceSingularHomologyMap_comp_augmentation])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoKernelSubspaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoKernelSubspaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoKernelSubspaceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoKernelSubspaceMap

noncomputable def relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    relativeSingularHomologyOfSubspace A 1 ⟶
      kernel (subspaceSingularHomologyMap A 0) :=
  kernel.lift
    (subspaceSingularHomologyMap A 0)
    (relativeSingularBoundary A 0)
    (by
      exact (relativeSingularChainSequence_shortExact A).δ_comp
        1 0 (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeBoundaryToKernelSubspaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeBoundaryToKernelSubspaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeBoundaryToKernelSubspaceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeBoundaryToKernelSubspaceMap

theorem epi_relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    Epi (relativeBoundaryToKernelSubspaceMap A) := by
  exact (relativeSingularHomology_exact_at_subspace A 0).epi_kernelLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.epi_relativeBoundaryToKernelSubspaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.epi_relativeBoundaryToKernelSubspaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.epi_relativeBoundaryToKernelSubspaceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.epi_relativeBoundaryToKernelSubspaceMap

theorem mono_relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hH1 : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of X) 1)) :
    Mono (relativeBoundaryToKernelSubspaceMap A) := by
  have habs : absoluteToRelativeSingularHomology A 1 = 0 :=
    hH1.eq_of_src _ _
  let _ : _root_.CategoryTheory.Mono (relativeSingularBoundary A 0) :=
    (relativeSingularHomology_exact_at_relative A 0).mono_g habs
  exact _root_.CategoryTheory.mono_of_mono_fac
    (kernel.lift_ι
      (subspaceSingularHomologyMap A 0)
      (relativeSingularBoundary A 0)
      (by
        exact (relativeSingularChainSequence_shortExact A).δ_comp
          1 0 (by simp)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_relativeBoundaryToKernelSubspaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_relativeBoundaryToKernelSubspaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_relativeBoundaryToKernelSubspaceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_relativeBoundaryToKernelSubspaceMap

theorem isIso_relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hH1 : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of X) 1)) :
    IsIso (relativeBoundaryToKernelSubspaceMap A) := by
  let _ : _root_.CategoryTheory.Epi (relativeBoundaryToKernelSubspaceMap A) :=
    epi_relativeBoundaryToKernelSubspaceMap A
  let _ : _root_.CategoryTheory.Mono (relativeBoundaryToKernelSubspaceMap A) :=
    mono_relativeBoundaryToKernelSubspaceMap A hH1
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeBoundaryToKernelSubspaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_relativeBoundaryToKernelSubspaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeBoundaryToKernelSubspaceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_relativeBoundaryToKernelSubspaceMap

noncomputable def relativeH1IsoReducedH0
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X)
    (hH1 : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of X) 1)) :
    relativeSingularHomologyOfSubspace A 1 ≅
      reducedSingularH0 (TopCat.of A) := by
  let _ := isIso_relativeBoundaryToKernelSubspaceMap A hH1
  exact _root_.CategoryTheory.asIso (relativeBoundaryToKernelSubspaceMap A) ≪≫
    (reducedSingularH0IsoKernelSubspaceMap A).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeH1IsoReducedH0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeH1IsoReducedH0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeH1IsoReducedH0 ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeH1IsoReducedH0

theorem reducedSingularH0IsoInt_of_relativeH1
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X)
    (hH1 : _root_.CategoryTheory.Limits.IsZero (integerSingularHomology (TopCat.of X) 1))
    (hrel : Nonempty
      (relativeSingularHomologyOfSubspace A 1 ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty
      (reducedSingularH0 (TopCat.of A) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := hrel
  exact ⟨(relativeH1IsoReducedH0 A hH1).symm ≪≫ e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoInt_of_relativeH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoInt_of_relativeH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoInt_of_relativeH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoInt_of_relativeH1


theorem isZero_integerSingularHomology_one_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (integerSingularHomology (TopCat.of X) 1) := by
  let e := singularChainsHomotopyEquivSingleZeroOfContractible X
  exact IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.down ℕ) 0
      (ModuleCat.of ℤ ℤ) 1 (by omega))
    (e.toHomologyIso 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_contractible ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_one_of_contractible

theorem hasAlexanderDualityH0Certificate_of_relativeH1
    (e : SphereTwo → EuclideanThree)
    (hrel : Nonempty
      (relativeSingularHomologyOfSubspace
          ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree) 1 ≅
        ModuleCat.of ℤ ℤ)) :
    HasAlexanderDualityH0Certificate e := by
  exact reducedSingularH0IsoInt_of_relativeH1
    ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree)
    (isZero_integerSingularHomology_one_of_contractible EuclideanThree)
    hrel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_relativeH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_relativeH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_relativeH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_relativeH1

end DifferentialGeometry.Topology.SphereSeparation
