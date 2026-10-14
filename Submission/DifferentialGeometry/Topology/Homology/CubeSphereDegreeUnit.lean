import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CubeSphereGenerator
import Submission.DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier
import Submission.DifferentialGeometry.Topology.Homology.IntegralReducedCoefficientBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Topology
open _root_.Submission.DifferentialGeometry.Homology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace DifferentialGeometry.Topology

def liftedSphereMap (n : ℕ) :
    C(liftedHomotopySphere.{u} n, Metric.sphere (0 : liftedSphereSpace.{u} n) 1) :=
  ⟨liftedSphereHomeomorph n, (liftedSphereHomeomorph n).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereMap ``Submission.DifferentialGeometry.Topology.liftedSphereMap

def euclideanToLiftedSphereMap :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      Metric.sphere (0 : liftedSphereSpace.{u} 2) 1) :=
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₜ
      Metric.sphere (0 : liftedSphereSpace.{u} 2) 1 :=
    Homeomorph.ulift.symm.trans (liftedSphereHomeomorph 2)
  ⟨e, e.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanToLiftedSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanToLiftedSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanToLiftedSphereMap ``Submission.DifferentialGeometry.Topology.euclideanToLiftedSphereMap

theorem euclideanToLiftedSphereMap_apply
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    euclideanToLiftedSphereMap.{u} z = liftedSphereHomeomorph 2 (ULift.up z) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanToLiftedSphereMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanToLiftedSphereMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanToLiftedSphereMap_apply ``Submission.DifferentialGeometry.Topology.euclideanToLiftedSphereMap_apply

def cubeSphereUnliftedLoop :
    GenLoop (Fin 3) (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)
      (liftedSphereMap.{u} 2 (ULift.up (cubeSphereBasepoint 2))) :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose (liftedSphereMap.{u} 2)
    (cubeSphereCollapse.{u} 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereUnliftedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereUnliftedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereUnliftedLoop ``Submission.DifferentialGeometry.Topology.cubeSphereUnliftedLoop

theorem cubeSphereUnliftedLoop_apply (t : Fin 3 → unitInterval) :
    cubeSphereUnliftedLoop.{u} t = euclideanToLiftedSphereMap.{u} (cubeSphereProjection 2 t) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereUnliftedLoop_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereUnliftedLoop_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereUnliftedLoop_apply ``Submission.DifferentialGeometry.Topology.cubeSphereUnliftedLoop_apply

theorem hurewiczCubeClass_cubeSphereUnliftedLoop :
    hurewiczCubeClass cubeSphereUnliftedLoop.{u} =
      integralHomologyMap 3 (liftedSphereMap.{u} 2) cubeSphereFundamentalClass.{u} :=
  hurewiczCubeClass_natural (liftedSphereMap.{u} 2) (cubeSphereCollapse.{u} 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczCubeClass_cubeSphereUnliftedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczCubeClass_cubeSphereUnliftedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczCubeClass_cubeSphereUnliftedLoop ``Submission.DifferentialGeometry.Topology.hurewiczCubeClass_cubeSphereUnliftedLoop

theorem integralLiftedSphereTopEquiv_cubeSphereFundamentalClass :
    integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass.{u} =
      integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2)
        (liftedSphereSpace_finrank 2) (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) := by
  rw [integralLiftedSphereTopEquiv, LinearEquiv.trans_apply]
  refine congrArg (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2)
    (liftedSphereSpace_finrank 2)) ?_
  exact (hurewiczCubeClass_cubeSphereUnliftedLoop.{u}).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLiftedSphereTopEquiv_cubeSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLiftedSphereTopEquiv_cubeSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLiftedSphereTopEquiv_cubeSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.integralLiftedSphereTopEquiv_cubeSphereFundamentalClass

theorem genLoopSphereHomeomorph_cubeSphereUnliftedLoop_val :
    (genLoopSphereHomeomorph 2 (liftedSphereMap.{u} 2 (ULift.up (cubeSphereBasepoint 2)))
      cubeSphereUnliftedLoop.{u}).val = euclideanToLiftedSphereMap.{u} := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨t, rfl⟩ := cubeSphereProjection_surjective 2 z
  rw [genLoopSphereHomeomorph_projection]
  exact cubeSphereUnliftedLoop_apply.{u} t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph_cubeSphereUnliftedLoop_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph_cubeSphereUnliftedLoop_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph_cubeSphereUnliftedLoop_val ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph_cubeSphereUnliftedLoop_val

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsUnit (integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass.{u}) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_coordinate]
  constructor
  · rintro (h | h)
    · rw [h]
      exact isUnit_one
    · rw [h]
      exact Int.isUnit_iff.mpr (Or.inr rfl)
  · intro h
    rcases Int.isUnit_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit

def liftedSphereReducedHomologyEquivThree :
    reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (liftedHomotopySphere.{0} 2)) 3 ≃ₗ[ℤ] ℤ :=
  (reducedSingularHomologyIso (ModuleCat.of ℤ ℤ)
      (Homeomorph.ulift.toHomotopyEquiv) 3).toLinearEquiv.trans
    (AddEquiv.toIntLinearEquiv
      (DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereReducedHomologyEquivThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereReducedHomologyEquivThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereReducedHomologyEquivThree ``Submission.DifferentialGeometry.Topology.liftedSphereReducedHomologyEquivThree

def cubeSphereReducedDegreeCoordinate :
    integralSingularHomology 3 (liftedHomotopySphere.{0} 2) ≃ₗ[ℤ] ℤ :=
  (integralReducedSingularHomologyEquiv 2 (liftedHomotopySphere.{0} 2)).trans
    liftedSphereReducedHomologyEquivThree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereReducedDegreeCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereReducedDegreeCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereReducedDegreeCoordinate ``Submission.DifferentialGeometry.Topology.cubeSphereReducedDegreeCoordinate

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_reducedDegreeCoordinate_isUnit :
    IsSphereHomologyGenerator.{0} 2 cubeSphereFundamentalClass.{0} ↔
      IsUnit (cubeSphereReducedDegreeCoordinate cubeSphereFundamentalClass.{0}) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit]
  exact (isUnit_apply_iff_isUnit_apply_of_linearEquiv cubeSphereReducedDegreeCoordinate
    (integralLiftedSphereTopEquiv.{0} 2) cubeSphereFundamentalClass.{0}).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_reducedDegreeCoordinate_isUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_reducedDegreeCoordinate_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_reducedDegreeCoordinate_isUnit ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_reducedDegreeCoordinate_isUnit

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsUnit (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2)
        (liftedSphereSpace_finrank 2) (hurewiczCubeClass cubeSphereUnliftedLoop.{u})) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit,
    integralLiftedSphereTopEquiv_cubeSphereFundamentalClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit

theorem cubeSphereFundamentalClass_ne_zero_of_reducedDegreeCoordinate_isUnit
    (h : IsUnit (cubeSphereReducedDegreeCoordinate cubeSphereFundamentalClass.{0})) :
    cubeSphereFundamentalClass.{0} ≠ 0 := by
  intro hzero
  rw [hzero, map_zero] at h
  exact not_isUnit_zero h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_reducedDegreeCoordinate_isUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_reducedDegreeCoordinate_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_reducedDegreeCoordinate_isUnit ``Submission.DifferentialGeometry.Topology.cubeSphereFundamentalClass_ne_zero_of_reducedDegreeCoordinate_isUnit

theorem not_exists_linearMap_eq_one_integralRelativeHomology_three_singleton_cube
    (b : Fin 3 → unitInterval)
    (z : integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval))) :
    ¬ ∃ φ : integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval)) →ₗ[ℤ] ℤ, φ z = 1 :=
  not_exists_linearMap_eq_one_of_subsingleton
    (subsingleton_integralRelativeHomology_three_singleton_cube b) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_three_singleton_cube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_three_singleton_cube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_three_singleton_cube ``Submission.DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_three_singleton_cube

theorem exists_relative_functional_liftedSphereGenerator_two :
    ∃ ψ : integralRelativeHomology 3
        ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative 3
        ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2))
        (integralLiftedSphereGenerator.{0} 2)) = 1 :=
  exists_relative_functional_integralLiftedSphereGenerator 2 (by norm_num)
    (ULift.up (cubeSphereBasepoint 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_relative_functional_liftedSphereGenerator_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_relative_functional_liftedSphereGenerator_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_relative_functional_liftedSphereGenerator_two ``Submission.DifferentialGeometry.Topology.exists_relative_functional_liftedSphereGenerator_two

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    (hg : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}) :
    HurewiczThreeMultiplicative X :=
  fun x _ c hc a b =>
    sphereHurewicz_mul_of_cubeSphereFundamentalClass_isSphereHomologyGenerator hg x c hc a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator ``Submission.DifferentialGeometry.Topology.hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator

end DifferentialGeometry.Topology
