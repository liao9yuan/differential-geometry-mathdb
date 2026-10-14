import Submission.DifferentialGeometry.Topology.Homology.ConeThreeSpherePairing
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronSphereCollapse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap _root_.Submission.ContinuousMap

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def integralSingularTetrahedronSphereClass (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (σ : integralSingularSimplex 3 X) :
    HomotopyGroup (Fin 3) X x :=
  Function.invFun
    (homotopyGroupSpherePrecompose 2 x Simplex.tetrahedronSphereCollapse)
    (integralSingularConeThreeSphereClass x σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass

theorem homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (σ : integralSingularSimplex 3 X) :
    homotopyGroupSpherePrecompose 2 x Simplex.tetrahedronSphereCollapse
      (integralSingularTetrahedronSphereClass x σ) =
        integralSingularConeThreeSphereClass x σ :=
  Function.rightInverse_invFun
    (Simplex.homotopyGroupSpherePrecompose_tetrahedronSphereCollapse_bijective x).surjective _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass

theorem integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (σ : integralSingularSimplex 3 X)
    (g : C(stdSimplex ℝ (Fin 4), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x)
    (h : (integralSingularConeThreeSphereMap x σ).Homotopic
      (Simplex.tetrahedronSphereMap g x hg)) :
    integralSingularTetrahedronSphereClass x σ =
      (⟦Simplex.tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) := by
  apply (Simplex.homotopyGroupSpherePrecompose_tetrahedronSphereCollapse_bijective x).injective
  rw [homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass,
    ← Simplex.tetrahedronSphereMap_class_eq_precompose]
  apply congrArg (homotopyGroupFreeSphereEquiv 2 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop

end DifferentialGeometry.Topology
