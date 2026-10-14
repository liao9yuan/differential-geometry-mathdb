import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Topology.Connected.LocallyPathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.Cardinal _root_.Function
open _root_.CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def reducedSingularH0 (X : TopCat) : ModuleCat ℤ :=
  _root_.CategoryTheory.Limits.kernel (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0 ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0

noncomputable def finsuppAugmentation (ι : Type*) : (ι →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ (fun _ => LinearMap.id)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation ``Submission.DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation

@[simp]
theorem finsuppAugmentation_single {ι : Type*} (i : ι) (z : ℤ) :
    finsuppAugmentation ι (Finsupp.single i z) = z := by
  simp [finsuppAugmentation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_single ``Submission.DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_single

theorem finsuppAugmentation_surjective {ι : Type*} [Nonempty ι] :
    Surjective (finsuppAugmentation ι) := by
  classical
  intro z
  exact ⟨Finsupp.single (Classical.arbitrary ι) z, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_surjective ``Submission.DifferentialGeometry.Topology.SphereSeparation.finsuppAugmentation_surjective

noncomputable def singularH0FinsuppIso (X : TopCat) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj X ≅
      ModuleCat.of ℤ (ZerothHomotopy X →₀ ℤ) := by
  classical
  exact X.singularHomology₀Iso (ModuleCat.of ℤ ℤ) ≪≫
    ModuleCat.coprodIsoDirectSum
      (fun _ : ZerothHomotopy X => ModuleCat.of ℤ ℤ) ≪≫
    (finsuppLEquivDirectSum ℤ ℤ (ZerothHomotopy X)).symm.toModuleIso

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso

theorem singularH0FinsuppIso_hom_comp_augmentation (X : TopCat) :
    (singularH0FinsuppIso X).hom ≫
        ModuleCat.ofHom (finsuppAugmentation (ZerothHomotopy X)) =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
  classical
  rw [← X.singularHomology₀Iso_sigma_desc_id (ModuleCat.of ℤ ℤ)]
  simp only [singularH0FinsuppIso, Iso.trans_hom, Category.assoc]
  apply (_root_.CategoryTheory.cancel_epi (X.singularHomology₀Iso (ModuleCat.of ℤ ℤ)).hom).mpr
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
  ext
  simp [finsuppAugmentation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso_hom_comp_augmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso_hom_comp_augmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso_hom_comp_augmentation ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularH0FinsuppIso_hom_comp_augmentation

noncomputable def reducedSingularH0IsoAugmentedFinsuppKernel (X : TopCat) :
    reducedSingularH0 X ≅
      ModuleCat.of ℤ
        (LinearMap.ker (finsuppAugmentation (ZerothHomotopy X))) :=
  kernel.mapIso
      (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))
      (ModuleCat.ofHom (finsuppAugmentation (ZerothHomotopy X)))
      (singularH0FinsuppIso X) (Iso.refl _)
      (by simpa using (singularH0FinsuppIso_hom_comp_augmentation X).symm) ≪≫
    ModuleCat.kernelIsoKer
      (ModuleCat.ofHom (finsuppAugmentation (ZerothHomotopy X)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoAugmentedFinsuppKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoAugmentedFinsuppKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoAugmentedFinsuppKernel ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoAugmentedFinsuppKernel

theorem nonempty_equiv_fin_two_of_augmentedFinsuppKernel_equiv_int
    {ι : Type*} [Nonempty ι]
    (h : Nonempty (LinearMap.ker (finsuppAugmentation ι) ≃ₗ[ℤ] ℤ)) :
    Nonempty (ι ≃ Fin 2) := by
  classical
  let e : LinearMap.ker (finsuppAugmentation ι) ≃ₗ[ℤ] ℤ := Classical.choice h
  have hrankKer : Module.rank ℤ (LinearMap.ker (finsuppAugmentation ι)) = 1 := by
    simpa [CommSemiring.rank_self] using e.lift_rank_eq
  have hrank :=
    (finsuppAugmentation ι).lift_rank_eq_of_surjective
      (finsuppAugmentation_surjective (ι := ι))
  have hrankSource : Module.rank ℤ (ι →₀ ℤ) = #ι := by
    simp
  have hrankLift : Cardinal.lift.{0} (Module.rank ℤ (ι →₀ ℤ)) = 2 := by
    simpa [CommSemiring.rank_self, hrankKer, one_add_one_eq_two] using hrank
  have hcard : #ι = 2 := by
    calc
      #ι = Module.rank ℤ (ι →₀ ℤ) := hrankSource.symm
      _ = 2 := by simpa using hrankLift
  exact Cardinal.mk_eq_nat_iff.mp hcard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonempty_equiv_fin_two_of_augmentedFinsuppKernel_equiv_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonempty_equiv_fin_two_of_augmentedFinsuppKernel_equiv_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonempty_equiv_fin_two_of_augmentedFinsuppKernel_equiv_int ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonempty_equiv_fin_two_of_augmentedFinsuppKernel_equiv_int

theorem zerothHomotopy_equiv_fin_two_of_reducedSingularH0_iso_int
    (X : TopCat) [Nonempty (ZerothHomotopy X)]
    (h : Nonempty (reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty (ZerothHomotopy X ≃ Fin 2) := by
  let e : reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ := Classical.choice h
  let e' := (reducedSingularH0IsoAugmentedFinsuppKernel X).symm ≪≫ e
  apply nonempty_equiv_fin_two_of_augmentedFinsuppKernel_equiv_int
  exact ⟨e'.toLinearEquiv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopy_equiv_fin_two_of_reducedSingularH0_iso_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.zerothHomotopy_equiv_fin_two_of_reducedSingularH0_iso_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopy_equiv_fin_two_of_reducedSingularH0_iso_int ``Submission.DifferentialGeometry.Topology.SphereSeparation.zerothHomotopy_equiv_fin_two_of_reducedSingularH0_iso_int

theorem connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int
    (X : TopCat) [Nonempty X] [LocallyPathConnectedSpace X]
    (h : Nonempty (reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty (ConnectedComponents X ≃ Fin 2) := by
  let _ : Nonempty (ZerothHomotopy X) :=
    Nonempty.map ZerothHomotopy.mk (inferInstance : Nonempty X)
  obtain ⟨e⟩ :=
    zerothHomotopy_equiv_fin_two_of_reducedSingularH0_iso_int X h
  exact ⟨connectedComponentsEquivZerothHomotopy.trans e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int ``Submission.DifferentialGeometry.Topology.SphereSeparation.connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int

end DifferentialGeometry.Topology.SphereSeparation
