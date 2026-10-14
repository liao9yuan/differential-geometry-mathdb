import Submission.DifferentialGeometry.Topology.Homology.TetrahedronSphereRelation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Submission.ContinuousMap
open scoped _root_.Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

omit [SimplyConnectedSpace X] in
private theorem constant_simplex_face (n : ℕ) (x : X) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i
      ((integralSingularSimplexEquiv (n + 1) X).symm (ContinuousMap.const _ x)) =
      (integralSingularSimplexEquiv n X).symm (ContinuousMap.const _ x) := by
  apply (integralSingularSimplexEquiv n X).injective
  ext p
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i
      ((integralSingularSimplexEquiv (n + 1) X).symm (ContinuousMap.const _ x))) p = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.constant_simplex_face
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.constant_simplex_face target :: scope.openDecls } }

theorem integralSingularTetrahedronSphereClass_const
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    integralSingularTetrahedronSphereClass x
      ((integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x)) = 1 := by
  have h := integralSingularTetrahedronSphereClass_face_relation x
    ((integralSingularSimplexEquiv 4 X).symm (ContinuousMap.const _ x))
  simp only [constant_simplex_face] at h
  exact (mul_eq_left.mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_const ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_const

theorem integralSingularConeThreeSphereClass_const
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    integralSingularConeThreeSphereClass x
      ((integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x)) = 1 := by
  rw [← homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass,
    integralSingularTetrahedronSphereClass_const, homotopyGroupSpherePrecompose_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeSphereClass_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeSphereClass_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeSphereClass_const ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeSphereClass_const

theorem integralSingularConeThreeSphereMap_const_homotopic
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    (integralSingularConeThreeSphereMap x
      ((integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x))).Homotopic
      (ContinuousMap.const _ x) := by
  have h := congrArg (homotopyGroupFreeSphereEquiv 2 x)
    (integralSingularConeThreeSphereClass_const x)
  change (homotopyGroupFreeSphereEquiv 2 x) ((homotopyGroupFreeSphereEquiv 2 x).symm _) =
    homotopyGroupToFreeSphere 2 x 1 at h
  rw [Equiv.apply_symm_apply, homotopyGroupToFreeSphere_one] at h
  exact (homotopic_iff_joined _ _).mpr (Quotient.exact h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_const_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_const_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_const_homotopic ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_const_homotopic

end DifferentialGeometry.Topology
