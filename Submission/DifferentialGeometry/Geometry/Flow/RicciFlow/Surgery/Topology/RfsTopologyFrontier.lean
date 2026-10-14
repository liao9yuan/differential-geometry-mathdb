import Submission.DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNormalization
import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCorePuncturedFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def RfsHurewiczFrontier (M : Type u) [TopologicalSpace M] : Prop :=
  Subsingleton (DifferentialGeometry.Topology.integralSingularHomology 2 M) ∧
    DifferentialGeometry.Topology.SphereHurewiczTwoCanonical M ∧
      DifferentialGeometry.Topology.SphereHurewiczThreeCanonical M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RfsHurewiczFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RfsHurewiczFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RfsHurewiczFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RfsHurewiczFrontier

def cubeSphereCollapseClassIsUnit : Prop :=
  DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
    DifferentialGeometry.Topology.cubeSphereFundamentalClass.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereCollapseClassIsUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereCollapseClassIsUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereCollapseClassIsUnit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereCollapseClassIsUnit

def squareSphereCollapseClassIsUnit : Prop :=
  DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1
    DifferentialGeometry.Topology.squareSphereFundamentalClass.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit

open _root_.Submission.DifferentialGeometry.Topology in
theorem squareSphereCollapseClassIsUnit_iff_exists_relativeFunctional :
    squareSphereCollapseClassIsUnit.{u} ↔
      ∃ ψ : DifferentialGeometry.Topology.integralRelativeHomology 2
          DifferentialGeometry.Topology.liftedSphereBasepoint.{u} →ₗ[ℤ] ℤ,
        ψ (DifferentialGeometry.Topology.integralAbsoluteToRelative 2
          DifferentialGeometry.Topology.liftedSphereBasepoint.{u}
          DifferentialGeometry.Topology.squareSphereFundamentalClass.{u}) = 1 :=
  squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit_iff_exists_relativeFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit_iff_exists_relativeFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit_iff_exists_relativeFunctional ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.squareSphereCollapseClassIsUnit_iff_exists_relativeFunctional

theorem exists_isSphereHomologyGenerator_one_liftedHomotopySphere :
    ∃ c : DifferentialGeometry.Topology.integralSingularHomology 2
        (DifferentialGeometry.Topology.liftedHomotopySphere.{u} 1),
      DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1 c :=
  ⟨DifferentialGeometry.Topology.integralLiftedSphereGenerator.{u} 1,
    DifferentialGeometry.Topology.integralLiftedSphereGenerator_isGenerator 1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isSphereHomologyGenerator_one_liftedHomotopySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isSphereHomologyGenerator_one_liftedHomotopySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isSphereHomologyGenerator_one_liftedHomotopySphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_isSphereHomologyGenerator_one_liftedHomotopySphere

variable {M : Type u} [TopologicalSpace M]

theorem subsingleton_homotopyGroup_two_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) :
    ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) :=
  fun q => (DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q h.1 hdeg h.2.1 h.2.2).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_homotopyGroup_two_of_hurewiczFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_homotopyGroup_two_of_hurewiczFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_homotopyGroup_two_of_hurewiczFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_homotopyGroup_two_of_hurewiczFrontier

theorem bijective_hurewiczThree_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) (q : M) :
    Function.Bijective (hurewiczThree q) :=
  (DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q h.1 hdeg h.2.1 h.2.2).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_hurewiczThree_of_hurewiczFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_hurewiczThree_of_hurewiczFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_hurewiczThree_of_hurewiczFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_hurewiczThree_of_hurewiczFrontier

theorem nonempty_mulEquiv_homotopyGroup_three_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) (q : M) :
    Nonempty (HomotopyGroup (Fin 3) M q ≃* Multiplicative (IntegralHomology M 3)) :=
  ⟨MulEquiv.ofBijective (hurewiczThreeHom q)
    (bijective_hurewiczThree_of_hurewiczFrontier h hdeg q)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_mulEquiv_homotopyGroup_three_of_hurewiczFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_mulEquiv_homotopyGroup_three_of_hurewiczFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_mulEquiv_homotopyGroup_three_of_hurewiczFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_mulEquiv_homotopyGroup_three_of_hurewiczFrontier

theorem rfsHurewiczFrontier_of_lowDegreeFrontier
    (h : DifferentialGeometry.Topology.HurewiczLowDegreeFrontier M)
    (hH₂ : Subsingleton (DifferentialGeometry.Topology.integralSingularHomology 2 M)) :
    RfsHurewiczFrontier M :=
  ⟨hH₂, h.1, h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_of_lowDegreeFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_of_lowDegreeFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_of_lowDegreeFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_of_lowDegreeFrontier

theorem rfsHurewiczFrontier_punit : RfsHurewiczFrontier PUnit.{u + 1} :=
  ⟨DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_contractible 2
      (by norm_num) PUnit.{u + 1},
    DifferentialGeometry.Topology.hurewiczLowDegreeFrontier_punit.1,
    DifferentialGeometry.Topology.hurewiczLowDegreeFrontier_punit.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_punit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfsHurewiczFrontier_punit

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem rfs_homotopy_groups_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) (o : TangentOrientationSection M) (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) := by
  let _ := o
  exact DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q h.1 hdeg h.2.1 h.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_hurewiczFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_hurewiczFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_hurewiczFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_hurewiczFrontier

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

def ChildSimplicityFrontier (E : SmoothCutCapTransition P Q D N) : Prop :=
  E.childCollaredStarCoverProducer ∧ E.ComponentwisePuncturedCoreOfParent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildSimplicityFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildSimplicityFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildSimplicityFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildSimplicityFrontier

theorem child_simplyConnected_of_childSimplicityFrontier (E : SmoothCutCapTransition P Q D N)
    (h : ChildSimplicityFrontier E) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_puncturedCoreProducer h.1 h.2 c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childSimplicityFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childSimplicityFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childSimplicityFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childSimplicityFrontier

theorem childSimplicityFrontier_of_isEmpty_childCapBoundary
    (E : SmoothCutCapTransition P Q D N)
    [∀ c : ConnectedComponents Q.Carrier, IsEmpty (E.ChildCapBoundary c)]
    (hcore : E.ChildCoreSimplyConnected) : ChildSimplicityFrontier E :=
  ⟨fun c _ => E.nonempty_childCarrierCollaredStarCover_of_isEmpty_childCapBoundary c,
    (E.componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent).mpr
      (E.childCoreSimplyConnectedOfParent_of_childCoreSimplyConnected hcore)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_isEmpty_childCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_isEmpty_childCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_isEmpty_childCapBoundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_isEmpty_childCapBoundary

theorem childSimplicityFrontier_of_childCoreSimplyConnected
    (E : SmoothCutCapTransition P Q D N) (hcover : E.childCollaredStarCoverProducer)
    (hcore : E.ChildCoreSimplyConnected) : ChildSimplicityFrontier E :=
  ⟨hcover,
    (E.componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent).mpr
      (E.childCoreSimplyConnectedOfParent_of_childCoreSimplyConnected hcore)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_childCoreSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_childCoreSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_childCoreSimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_of_childCoreSimplyConnected

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
