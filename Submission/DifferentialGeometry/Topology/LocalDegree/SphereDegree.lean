import Submission.DifferentialGeometry.Topology.LocalDegree.SphereGenerator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology
variable {d : ℕ}


def euclideanSphereDegree (f : C(EuclideanSphere d, EuclideanSphere d)) : ℤ :=
  euclideanSphereTopReducedHomologyEquiv d
    (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d
      (euclideanSphereTopGenerator d))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree


theorem euclideanSphereDegree_generator (f : C(EuclideanSphere d, EuclideanSphere d)) :
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d
        (euclideanSphereTopGenerator d) =
      euclideanSphereDegree f • euclideanSphereTopGenerator d :=
  (euclideanSphereTopReducedHomologyEquiv_smul_generator d _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_generator ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_generator


theorem euclideanSphereDegree_action (f : C(EuclideanSphere d, EuclideanSphere d))
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d) :
    euclideanSphereTopReducedHomologyEquiv d
        (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d c) =
      euclideanSphereDegree f * euclideanSphereTopReducedHomologyEquiv d c := by
  rw [← euclideanSphereTopReducedHomologyEquiv_smul_generator d c]
  simp only [map_zsmul, euclideanSphereDegree, smul_eq_mul,
    euclideanSphereTopReducedHomologyEquiv_generator, mul_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_action then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_action"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_action ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_action


@[simp]
theorem euclideanSphereDegree_id :
    euclideanSphereDegree (ContinuousMap.id (EuclideanSphere d)) = 1 := by
  unfold euclideanSphereDegree
  rw [show TopCat.ofHom (ContinuousMap.id (EuclideanSphere d)) = 𝟙 _ from rfl,
    reducedSingularHomologyMap_id]
  exact euclideanSphereTopReducedHomologyEquiv_generator d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_id ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_id


theorem euclideanSphereDegree_comp (f g : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereDegree (g.comp f) = euclideanSphereDegree g * euclideanSphereDegree f := by
  unfold euclideanSphereDegree
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl,
    reducedSingularHomologyMap_comp]
  exact euclideanSphereDegree_action g _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_comp ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_comp


theorem euclideanSphereDegree_eq_of_homotopy
    {f g : C(EuclideanSphere d, EuclideanSphere d)} (H : f.Homotopy g) :
    euclideanSphereDegree f = euclideanSphereDegree g := by
  unfold euclideanSphereDegree
  rw [reducedSingularHomologyMap_eq_of_homotopy (ModuleCat.of ℤ ℤ) H]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_eq_of_homotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_eq_of_homotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_eq_of_homotopy ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_eq_of_homotopy


@[simp]
theorem euclideanSphereDegree_const (y : EuclideanSphere d) :
    euclideanSphereDegree (ContinuousMap.const (EuclideanSphere d) y) = 0 := by
  let p : TopCat.of (EuclideanSphere d) ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let q : TopCat.of PUnit ⟶ TopCat.of (EuclideanSphere d) := TopCat.ofHom (ContinuousMap.const _ y)
  have hz := isZero_reducedSingularHomology_of_contractible (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) d
  have hp : reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) p d = 0 := hz.eq_of_tgt _ _
  unfold euclideanSphereDegree
  rw [show TopCat.ofHom (ContinuousMap.const (EuclideanSphere d) y) = p ≫ q from rfl,
    reducedSingularHomologyMap_comp, hp, _root_.CategoryTheory.Limits.zero_comp]
  exact map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_const ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_const


theorem euclideanSphereDegree_isUnit
    (e : ContinuousMap.HomotopyEquiv (EuclideanSphere d) (EuclideanSphere d)) :
    IsUnit (euclideanSphereDegree e.toFun) := by
  obtain ⟨H⟩ := e.left_inv
  have he := euclideanSphereDegree_eq_of_homotopy H
  rw [euclideanSphereDegree_comp, euclideanSphereDegree_id] at he
  exact isUnit_of_dvd_one ⟨euclideanSphereDegree e.invFun, by rw [mul_comm]; exact he.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_isUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_isUnit ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_isUnit

end DifferentialGeometry.LocalDegree
