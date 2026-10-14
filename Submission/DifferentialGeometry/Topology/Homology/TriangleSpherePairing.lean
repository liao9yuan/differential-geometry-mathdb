import Submission.DifferentialGeometry.Topology.Homology.ConeSpherePairing
import Submission.DifferentialGeometry.Topology.Simplex.TriangleSphereCollapse

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

def integralSingularTriangleSphereClass (x : X) (σ : integralSingularSimplex 2 X) :
    HomotopyGroup (Fin 2) X x :=
  Function.invFun
    (homotopyGroupSpherePrecompose 1 x Simplex.triangleSphereCollapse)
    (integralSingularConeSphereClass x σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTriangleSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTriangleSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTriangleSphereClass ``Submission.DifferentialGeometry.Topology.integralSingularTriangleSphereClass

theorem homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass
    (x : X) (σ : integralSingularSimplex 2 X) :
    homotopyGroupSpherePrecompose 1 x Simplex.triangleSphereCollapse
      (integralSingularTriangleSphereClass x σ) =
        integralSingularConeSphereClass x σ :=
  Function.rightInverse_invFun
    (Simplex.homotopyGroupSpherePrecompose_triangleSphereCollapse_bijective x).surjective _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass ``Submission.DifferentialGeometry.Topology.homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass

theorem integralSingularTriangleSphereClass_eq_triangleGenLoop
    (x : X) (σ : integralSingularSimplex 2 X)
    (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x)
    (h : (integralSingularConeSphereMap x σ).Homotopic
      (Simplex.triangleSphereMap g x hg)) :
    integralSingularTriangleSphereClass x σ =
      (⟦Simplex.triangleGenLoop g x hg⟧ : HomotopyGroup (Fin 2) X x) := by
  apply (Simplex.homotopyGroupSpherePrecompose_triangleSphereCollapse_bijective x).injective
  rw [homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass,
    ← Simplex.triangleSphereMap_class_eq_precompose]
  apply congrArg (homotopyGroupFreeSphereEquiv 1 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTriangleSphereClass_eq_triangleGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTriangleSphereClass_eq_triangleGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTriangleSphereClass_eq_triangleGenLoop ``Submission.DifferentialGeometry.Topology.integralSingularTriangleSphereClass_eq_triangleGenLoop

end DifferentialGeometry.Topology
