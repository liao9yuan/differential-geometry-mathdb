import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Submission.DifferentialGeometry.Topology.SphereSeparation.JordanBrouwer
import Submission.DifferentialGeometry.Topology.SphereSeparation.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation


abbrev integerDual (M : ModuleCat ℤ) := Module.Dual ℤ M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerDual ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerDual

def dualDifferential {M N : ModuleCat ℤ} (d : N ⟶ M) :
    integerDual M →ₗ[ℤ] integerDual N :=
  Module.Dual.transpose d.hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualDifferential ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualDifferential

@[simp]
theorem dualDifferential_apply {M N : ModuleCat ℤ} (d : N ⟶ M)
    (f : integerDual M) (x : N) :
    dualDifferential d f x = f (d x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualDifferential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualDifferential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualDifferential_apply ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualDifferential_apply


noncomputable def dualCochainComplex (C : ChainComplex (ModuleCat ℤ) ℕ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of ℤ (integerDual (C.X n)))
    (fun n => ModuleCat.ofHom (dualDifferential (C.d (n + 1) n)))
    (fun n => by
      ext f x
      change f (C.d (n + 1) n (C.d (n + 2) (n + 1) x)) = (0 : ℤ)
      have hdd : C.d (n + 2) (n + 1) ≫ C.d (n + 1) n = 0 :=
        C.d_comp_d (n + 2) (n + 1) n
      have hx : C.d (n + 1) n (C.d (n + 2) (n + 1) x) = 0 := by
        change (C.d (n + 2) (n + 1) ≫ C.d (n + 1) n) x = 0
        rw [hdd]
        rfl
      rw [hx]
      exact map_zero f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainComplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainComplex


noncomputable def singularCochainComplex (X : TopCat) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  dualCochainComplex
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCochainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCochainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCochainComplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCochainComplex

noncomputable def singularCohomology (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  (singularCochainComplex X).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCohomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCohomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCohomology ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCohomology


noncomputable def dualCochainMap {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) :
    dualCochainComplex D ⟶ dualCochainComplex C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (dualDifferential (f.f n)))
    (fun n => by
      dsimp only [dualCochainComplex]
      simp only [CochainComplex.of_d]
      ext φ x
      change φ (f.f n (C.d (n + 1) n x)) =
        φ (D.d (n + 1) n (f.f (n + 1) x))
      have hcomm := f.comm (n + 1) n
      have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcomm) x
      exact congrArg φ hx.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainMap


noncomputable def singularCochainMap {X Y : TopCat} (f : X ⟶ Y) :
    singularCochainComplex Y ⟶ singularCochainComplex X :=
  dualCochainMap
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCochainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCochainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCochainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCochainMap

@[simp]
theorem dualCochainMap_id (C : ChainComplex (ModuleCat ℤ) ℕ) :
    dualCochainMap (𝟙 C) = 𝟙 (dualCochainComplex C) := by
  apply HomologicalComplex.hom_ext
  intro n
  ext φ
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_id ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_id

@[simp]
theorem dualCochainMap_comp
    {C D E : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (g : D ⟶ E) :
    dualCochainMap (f ≫ g) = dualCochainMap g ≫ dualCochainMap f := by
  apply HomologicalComplex.hom_ext
  intro n
  ext φ
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_comp ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_comp

noncomputable def dualCochainIso
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : C ≅ D) :
    dualCochainComplex D ≅ dualCochainComplex C where
  hom := dualCochainMap e.hom
  inv := dualCochainMap e.inv
  hom_inv_id := by
    rw [← dualCochainMap_comp, e.inv_hom_id, dualCochainMap_id]
  inv_hom_id := by
    rw [← dualCochainMap_comp, e.hom_inv_id, dualCochainMap_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainIso

noncomputable def singularCochainIsoOfHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    singularCochainComplex (TopCat.of Y) ≅
      singularCochainComplex (TopCat.of X) :=
  dualCochainIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCochainIsoOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCochainIsoOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCochainIsoOfHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCochainIsoOfHomeomorph


noncomputable def singularCohomologyIsoOfHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    singularCohomology (TopCat.of Y) n ≅
      singularCohomology (TopCat.of X) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
    (singularCochainIsoOfHomeomorph e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomeomorph



noncomputable def finTwoAugmentationKernelEquivInt :
    LinearMap.ker (finsuppAugmentation (Fin 2)) ≃ₗ[ℤ] ℤ where
  toFun x := x.1 0
  invFun z := ⟨Finsupp.single 0 z - Finsupp.single 1 z, by simp⟩
  map_add' x y := by simp
  map_smul' z x := by simp
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · have hx := x.2
      simp only [LinearMap.mem_ker] at hx
      change finsuppAugmentation (Fin 2) x.1 = 0 at hx
      rw [show finsuppAugmentation (Fin 2) x.1 = x.1 0 + x.1 1 by
        classical
        simp [finsuppAugmentation, Finsupp.sum_fintype]] at hx
      simpa using (eq_neg_of_add_eq_zero_right hx).symm
  right_inv z := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.finTwoAugmentationKernelEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.finTwoAugmentationKernelEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.finTwoAugmentationKernelEquivInt ``Submission.DifferentialGeometry.Topology.SphereSeparation.finTwoAugmentationKernelEquivInt

theorem finsuppAugmentation_domLCongr {ι κ : Type*} (e : ι ≃ κ)
    (x : ι →₀ ℤ) :
    finsuppAugmentation κ
        ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) x) =
      finsuppAugmentation ι x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      calc
        finsuppAugmentation κ
            ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) (f + g)) =
            finsuppAugmentation κ
              ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) f +
                (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) g) := by rw [map_add]
        _ = finsuppAugmentation κ
              ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) f) +
            finsuppAugmentation κ
              ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) g) := by rw [map_add]
        _ = finsuppAugmentation ι f + finsuppAugmentation ι g := by rw [hf, hg]
        _ = finsuppAugmentation ι (f + g) := by rw [map_add]
  | single i z => simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_domLCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_domLCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_domLCongr ``Submission.DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_domLCongr

noncomputable def augmentationKernelCongr {ι κ : Type*} (e : ι ≃ κ) :
    LinearMap.ker (finsuppAugmentation ι) ≃ₗ[ℤ]
      LinearMap.ker (finsuppAugmentation κ) where
  toFun x := ⟨(Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) x.1, by
    rw [LinearMap.mem_ker]
    rw [finsuppAugmentation_domLCongr]
    exact x.2⟩
  invFun x := ⟨(Finsupp.domLCongr e.symm : (κ →₀ ℤ) ≃ₗ[ℤ] (ι →₀ ℤ)) x.1, by
    rw [LinearMap.mem_ker]
    rw [finsuppAugmentation_domLCongr]
    exact x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simpa using
      (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).map_add x.1 y.1
  map_smul' z x := by
    apply Subtype.ext
    exact
      (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).map_smul z x.1
  left_inv x := by
    apply Subtype.ext
    exact (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).apply_symm_apply x.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.augmentationKernelCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.augmentationKernelCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.augmentationKernelCongr ``Submission.DifferentialGeometry.Topology.SphereSeparation.augmentationKernelCongr

noncomputable def augmentationKernelEquivIntOfEquivFinTwo {ι : Type*}
    (e : ι ≃ Fin 2) :
    LinearMap.ker (finsuppAugmentation ι) ≃ₗ[ℤ] ℤ :=
  augmentationKernelCongr e ≪≫ₗ finTwoAugmentationKernelEquivInt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.augmentationKernelEquivIntOfEquivFinTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.augmentationKernelEquivIntOfEquivFinTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.augmentationKernelEquivIntOfEquivFinTwo ``Submission.DifferentialGeometry.Topology.SphereSeparation.augmentationKernelEquivIntOfEquivFinTwo

noncomputable def reducedSingularH0IsoIntOfZerothHomotopyEquiv
    (X : TopCat) (e : ZerothHomotopy X ≃ Fin 2) :
    reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularH0IsoAugmentedFinsuppKernel X ≪≫
    (augmentationKernelEquivIntOfEquivFinTwo e).toModuleIso

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoIntOfZerothHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoIntOfZerothHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoIntOfZerothHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoIntOfZerothHomotopyEquiv

theorem reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two
    (X : TopCat) [LocallyPathConnectedSpace X]
    (e : ConnectedComponents X ≃ Fin 2) :
    Nonempty (reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ) :=
  ⟨reducedSingularH0IsoIntOfZerothHomotopyEquiv X
    (connectedComponentsEquivZerothHomotopy.symm.trans e)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two

theorem standardSphere_hasAlexanderDualityH0Certificate :
    HasAlexanderDualityH0Certificate
      (Subtype.val : SphereTwo → EuclideanThree) := by
  have hrange :
      Set.range (Subtype.val : SphereTwo → EuclideanThree) =
        Metric.sphere (0 : EuclideanThree) 1 := by
    ext x
    simp
  let X := ((Metric.sphere (0 : EuclideanThree) 1)ᶜ : Set EuclideanThree)
  let _ : LocallyPathConnectedSpace X :=
    Metric.isClosed_sphere.isOpen_compl.locallyPathConnectedSpace
  have h := reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two
    (TopCat.of X) standardUnitSphereComplementComponents
  unfold HasAlexanderDualityH0Certificate
  rw [hrange]
  have hcompl :
      ({x : EuclideanThree | x ∉ Metric.sphere (0 : EuclideanThree) 1} :
          Set EuclideanThree) =
        (Metric.sphere (0 : EuclideanThree) 1)ᶜ := rfl
  rw [hcompl]
  simpa only [X] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.standardSphere_hasAlexanderDualityH0Certificate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.standardSphere_hasAlexanderDualityH0Certificate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.standardSphere_hasAlexanderDualityH0Certificate ``Submission.DifferentialGeometry.Topology.SphereSeparation.standardSphere_hasAlexanderDualityH0Certificate



def embeddedSphereInOnePoint (e : SphereTwo → EuclideanThree) :
    Set (OnePoint EuclideanThree) :=
  ((↑) : EuclideanThree → OnePoint EuclideanThree) '' Set.range e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePoint

theorem compl_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree) :
    (embeddedSphereInOnePoint e)ᶜ =
      ((↑) : EuclideanThree → OnePoint EuclideanThree) ''
          (Set.range e)ᶜ ∪ {OnePoint.infty} := by
  exact OnePoint.compl_image_coe (Set.range e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compl_embeddedSphereInOnePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compl_embeddedSphereInOnePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compl_embeddedSphereInOnePoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.compl_embeddedSphereInOnePoint

theorem isCompact_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsCompact (embeddedSphereInOnePoint e) := by
  exact (isCompact_range he.contMDiff.continuous).image OnePoint.continuous_coe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isCompact_embeddedSphereInOnePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isCompact_embeddedSphereInOnePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isCompact_embeddedSphereInOnePoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.isCompact_embeddedSphereInOnePoint

theorem isClosed_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsClosed (embeddedSphereInOnePoint e) :=
  (isCompact_embeddedSphereInOnePoint e he).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isClosed_embeddedSphereInOnePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isClosed_embeddedSphereInOnePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isClosed_embeddedSphereInOnePoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.isClosed_embeddedSphereInOnePoint

noncomputable def sphereTwoHomeomorphEmbeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    SphereTwo ≃ₜ embeddedSphereInOnePoint e := by
  let f : SphereTwo → OnePoint EuclideanThree := fun x => (e x : OnePoint EuclideanThree)
  have hf : Topology.IsEmbedding f :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp he.isEmbedding
  have hrange : Set.range f = embeddedSphereInOnePoint e := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hrange)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoHomeomorphEmbeddedSphereInOnePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoHomeomorphEmbeddedSphereInOnePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoHomeomorphEmbeddedSphereInOnePoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoHomeomorphEmbeddedSphereInOnePoint

def alexanderDualityCompactum (e : SphereTwo → EuclideanThree) :
    Set (OnePoint EuclideanThree) :=
  embeddedSphereInOnePoint e ∪ {OnePoint.infty}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactum ``Submission.DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactum

theorem compl_alexanderDualityCompactum
    (e : SphereTwo → EuclideanThree) :
    (alexanderDualityCompactum e)ᶜ =
      ((↑) : EuclideanThree → OnePoint EuclideanThree) ''
        (Set.range e)ᶜ := by
  ext y
  induction y using OnePoint.rec with
  | infty => simp [alexanderDualityCompactum, embeddedSphereInOnePoint]
  | coe y => simp [alexanderDualityCompactum, embeddedSphereInOnePoint]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compl_alexanderDualityCompactum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compl_alexanderDualityCompactum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compl_alexanderDualityCompactum ``Submission.DifferentialGeometry.Topology.SphereSeparation.compl_alexanderDualityCompactum


theorem isCompact_alexanderDualityCompactum
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsCompact (alexanderDualityCompactum e) :=
  (isCompact_embeddedSphereInOnePoint e he).union isCompact_singleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isCompact_alexanderDualityCompactum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isCompact_alexanderDualityCompactum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isCompact_alexanderDualityCompactum ``Submission.DifferentialGeometry.Topology.SphereSeparation.isCompact_alexanderDualityCompactum


theorem isClosed_alexanderDualityCompactum
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsClosed (alexanderDualityCompactum e) :=
  (isCompact_alexanderDualityCompactum e he).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isClosed_alexanderDualityCompactum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isClosed_alexanderDualityCompactum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isClosed_alexanderDualityCompactum ``Submission.DifferentialGeometry.Topology.SphereSeparation.isClosed_alexanderDualityCompactum


def compactumInfinity (e : SphereTwo → EuclideanThree) :
    alexanderDualityCompactum e :=
  ⟨OnePoint.infty, Or.inr rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compactumInfinity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compactumInfinity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compactumInfinity ``Submission.DifferentialGeometry.Topology.SphereSeparation.compactumInfinity


def compactumInfinityNeighborhood (e : SphereTwo → EuclideanThree) :
    Set (alexanderDualityCompactum e) :=
  (Subtype.val : alexanderDualityCompactum e → OnePoint EuclideanThree) ⁻¹'
    (embeddedSphereInOnePoint e)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood ``Submission.DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood

theorem isOpen_compactumInfinityNeighborhood
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsOpen (compactumInfinityNeighborhood e) := by
  exact (isClosed_embeddedSphereInOnePoint e he).isOpen_compl.preimage
    continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpen_compactumInfinityNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpen_compactumInfinityNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpen_compactumInfinityNeighborhood ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpen_compactumInfinityNeighborhood


theorem compactumInfinityNeighborhood_eq_singleton
    (e : SphereTwo → EuclideanThree) :
    compactumInfinityNeighborhood e = {compactumInfinity e} := by
  ext x
  constructor
  · intro hx
    apply Subtype.ext
    rcases x.property with hxA | hxInf
    · exact (hx hxA).elim
    · exact hxInf
  · intro hx
    have hxEq : x = compactumInfinity e := by simpa using hx
    subst x
    exact OnePoint.infty_notMem_image_coe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood_eq_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood_eq_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood_eq_singleton ``Submission.DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhood_eq_singleton

noncomputable def homeomorphSumComplOfIsClopen
    {X : Type*} [TopologicalSpace X] (s : Set X) (hs : IsClopen s) :
    s ⊕ (sᶜ : Set X) ≃ₜ X := by
  classical
  exact (Equiv.Set.sumCompl s).toHomeomorphOfContinuousOpen
    (continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_subtype_val⟩)
    (isOpenMap_sum.mpr
      ⟨hs.isOpen.isOpenMap_subtype_val,
        hs.isClosed.isOpen_compl.isOpenMap_subtype_val⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.homeomorphSumComplOfIsClopen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.homeomorphSumComplOfIsClopen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.homeomorphSumComplOfIsClopen ``Submission.DifferentialGeometry.Topology.SphereSeparation.homeomorphSumComplOfIsClopen


noncomputable def compactumInfinityNeighborhoodHomeomorphPUnit
    (e : SphereTwo → EuclideanThree) :
    compactumInfinityNeighborhood e ≃ₜ PUnit :=
  (Homeomorph.setCongr (compactumInfinityNeighborhood_eq_singleton e)).trans
    (Homeomorph.homeomorphOfUnique _ PUnit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhoodHomeomorphPUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhoodHomeomorphPUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhoodHomeomorphPUnit ``Submission.DifferentialGeometry.Topology.SphereSeparation.compactumInfinityNeighborhoodHomeomorphPUnit

noncomputable def compactumAwayFromInfinityHomeomorphEmbeddedSphere
    (e : SphereTwo → EuclideanThree) :
    ((compactumInfinityNeighborhood e)ᶜ :
        Set (alexanderDualityCompactum e)) ≃ₜ
      embeddedSphereInOnePoint e := by
  let f : ((compactumInfinityNeighborhood e)ᶜ :
      Set (alexanderDualityCompactum e)) → OnePoint EuclideanThree :=
    fun x => x.1.1
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range f = embeddedSphereInOnePoint e := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rcases x.1.property with hxA | hxInf
      · exact hxA
      · exfalso
        exact x.2 (by
          change x.1.1 ∉ embeddedSphereInOnePoint e
          rw [Set.mem_singleton_iff] at hxInf
          rw [hxInf]
          exact OnePoint.infty_notMem_image_coe)
    · intro hy
      let x : alexanderDualityCompactum e := ⟨y, Or.inl hy⟩
      have hx : x ∉ compactumInfinityNeighborhood e := by
        intro hx'
        exact hx' hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hrange)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compactumAwayFromInfinityHomeomorphEmbeddedSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compactumAwayFromInfinityHomeomorphEmbeddedSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compactumAwayFromInfinityHomeomorphEmbeddedSphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.compactumAwayFromInfinityHomeomorphEmbeddedSphere

noncomputable def sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    SphereTwo ⊕ PUnit ≃ₜ alexanderDualityCompactum e := by
  have hclopen : IsClopen (compactumInfinityNeighborhood e) := by
    constructor
    · rw [compactumInfinityNeighborhood_eq_singleton]
      exact isClosed_singleton
    · exact isOpen_compactumInfinityNeighborhood e he
  exact (Homeomorph.sumComm SphereTwo PUnit).trans
    ((Homeomorph.sumCongr
      (compactumInfinityNeighborhoodHomeomorphPUnit e).symm
      ((sphereTwoHomeomorphEmbeddedSphereInOnePoint e he).trans
        (compactumAwayFromInfinityHomeomorphEmbeddedSphere e).symm)).trans
      (homeomorphSumComplOfIsClopen (compactumInfinityNeighborhood e) hclopen))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum

noncomputable def alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2 ≅
      singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 :=
  singularCohomologyIsoOfHomeomorph
    (sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum e he) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit ``Submission.DifferentialGeometry.Topology.SphereSeparation.alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit

theorem hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hduality : Nonempty
      (reducedSingularH0
          (TopCat.of {x : EuclideanThree | x ∉ Set.range e}) ≅
        singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2))
    (hsphere : Nonempty
      (singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
        ModuleCat.of ℤ ℤ)) :
    HasAlexanderDualityH0Certificate e := by
  obtain ⟨duality⟩ := hduality
  obtain ⟨sphereCohomology⟩ := hsphere
  exact ⟨duality ≪≫
    alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit e he ≪≫
    sphereCohomology⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology

noncomputable def onePointEuclideanThreeHomeomorphSphereThree :
    OnePoint EuclideanThree ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  onePointEquivSphereOfFinrankEq (by
    norm_num [EuclideanThree, Module.finrank_fin_fun])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.onePointEuclideanThreeHomeomorphSphereThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.onePointEuclideanThreeHomeomorphSphereThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.onePointEuclideanThreeHomeomorphSphereThree ``Submission.DifferentialGeometry.Topology.SphereSeparation.onePointEuclideanThreeHomeomorphSphereThree

theorem infty_mem_compl_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree) :
    OnePoint.infty ∈ (embeddedSphereInOnePoint e)ᶜ := by
  exact OnePoint.infty_notMem_image_coe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.infty_mem_compl_embeddedSphereInOnePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.infty_mem_compl_embeddedSphereInOnePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.infty_mem_compl_embeddedSphereInOnePoint ``Submission.DifferentialGeometry.Topology.SphereSeparation.infty_mem_compl_embeddedSphereInOnePoint

noncomputable def embeddedSphereInOnePointCohomologyIsoSphereTwo
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (n : ℕ) :
    singularCohomology (TopCat.of (embeddedSphereInOnePoint e)) n ≅
      singularCohomology (TopCat.of SphereTwo) n :=
  singularCohomologyIsoOfHomeomorph
    (sphereTwoHomeomorphEmbeddedSphereInOnePoint e he) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePointCohomologyIsoSphereTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePointCohomologyIsoSphereTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePointCohomologyIsoSphereTwo ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereInOnePointCohomologyIsoSphereTwo

end DifferentialGeometry.Topology.SphereSeparation
