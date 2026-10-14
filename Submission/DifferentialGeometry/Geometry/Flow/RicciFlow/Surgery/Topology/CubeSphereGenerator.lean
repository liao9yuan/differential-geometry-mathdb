import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge
import Submission.DifferentialGeometry.Topology.Homology.LiftedSphere
import Submission.DifferentialGeometry.Topology.Homology.SpherePuncture
import Submission.DifferentialGeometry.Topology.Homology.TwoSetCoverSubdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory

namespace DifferentialGeometry.Topology

universe u

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_functional
    (φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ)
    (hφ : Function.Surjective φ) (h1 : φ cubeSphereFundamentalClass = 1) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass :=
  (isSphereHomologyGenerator_iff_exists_surjective_functional 2
    cubeSphereFundamentalClass).mpr ⟨φ, hφ, h1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_functional ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_of_functional

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_exists_functional :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass ↔
      ∃ φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ,
        Function.Surjective φ ∧ φ cubeSphereFundamentalClass = 1 :=
  isSphereHomologyGenerator_iff_exists_surjective_functional 2 cubeSphereFundamentalClass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_exists_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_exists_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_exists_functional ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_exists_functional

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_forall_exists_zsmul :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass ↔
      ∀ x : integralSingularHomology 3 (liftedHomotopySphere.{u} 2),
        ∃ k : ℤ, x = k • cubeSphereFundamentalClass :=
  isSphereHomologyGenerator_iff_forall_exists_zsmul 2 cubeSphereFundamentalClass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_forall_exists_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_forall_exists_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_forall_exists_zsmul ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_forall_exists_zsmul

attribute [local instance] spherePuncture_contractible

theorem exists_cubeSphereFundamentalClass_cover_intersection_chain
    (v : Metric.sphere (0 : liftedSphereSpace.{u} 2) 1) :
    ∃ (a : integralSingularCoefficients ⟶
        (integralSingularChains (subspaceIntersection
          ({v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
          ({-v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)))).X 2)
      (ha : a ≫ (integralSingularChains (subspaceIntersection
        ({v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
        ({-v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)))).d 2 1 = 0),
      integralHomologyContractibleCoverEquiv 1
          ({v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
          ({-v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
          isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)
          (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeClass
            (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose
              (liftedSphereHomeomorph 2).toHomotopyEquiv.toFun (cubeSphereCollapse 2))) =
        (((integralSingularChains (subspaceIntersection
          ({v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
          ({-v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)))).liftCycles a 1
          ((ComplexShape.down ℕ).next_eq' (by rfl)) ha ≫
          (integralSingularChains (subspaceIntersection
            ({v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
            ({-v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)))).homologyπ 2)
          (ULift.up 1)) := by
  exact exists_integralHomologyContractibleCoverEquiv_liftCycles_eq 1
    ({v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
    ({-v}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1))
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)
    (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain
      (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose
        (liftedSphereHomeomorph 2).toHomotopyEquiv.toFun (cubeSphereCollapse 2)))
    (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain_boundary
      (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose
        (liftedSphereHomeomorph 2).toHomotopyEquiv.toFun (cubeSphereCollapse 2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_cubeSphereFundamentalClass_cover_intersection_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_cubeSphereFundamentalClass_cover_intersection_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_cubeSphereFundamentalClass_cover_intersection_chain ``Submission.DifferentialGeometry.Topology.exists_cubeSphereFundamentalClass_cover_intersection_chain

end DifferentialGeometry.Topology
