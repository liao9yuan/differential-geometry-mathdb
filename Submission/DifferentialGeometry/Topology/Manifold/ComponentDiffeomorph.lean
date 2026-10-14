import Submission.DifferentialGeometry.Topology.Manifold.Components
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u v
variable {n : ℕ} {M : ClosedOrientedManifold.{u} n} {N : ClosedOrientedManifold.{v} n}

private theorem componentMap_cancel
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) :
    e.symm.continuous.connectedComponentsMap (e.continuous.connectedComponentsMap C) = C := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [Continuous.connectedComponentsMap_mk e.continuous x,
    Continuous.connectedComponentsMap_mk e.symm.continuous (e x), e.symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentMap_cancel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ClosedOrientedManifold.componentMap_cancel target :: scope.openDecls } }

private theorem componentMap_mem
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    ConnectedComponents.mk (e x.val) = e.continuous.connectedComponentsMap C :=
  congrArg e.continuous.connectedComponentsMap x.property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentMap_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ClosedOrientedManifold.componentMap_mem target :: scope.openDecls } }

private theorem componentMap_inv_mem
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier)
    (y : N.componentOpen (e.continuous.connectedComponentsMap C)) :
    ConnectedComponents.mk (e.symm y.val) = C :=
  (congrArg e.symm.continuous.connectedComponentsMap y.property).trans (componentMap_cancel e C)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentMap_inv_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ClosedOrientedManifold.componentMap_inv_mem target :: scope.openDecls } }

def diffeomorphComponent
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) :
    M.componentOpen C ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      N.componentOpen (e.continuous.connectedComponentsMap C) where
  toEquiv :=
    { toFun := fun x => ⟨e x.val, componentMap_mem e C x⟩
      invFun := fun y => ⟨e.symm y.val, componentMap_inv_mem e C y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val) }
  contMDiff_toFun := by
    intro x
    exact DifferentialGeometry.codRestr_contMDiffAt
      (V := N.componentOpen (e.continuous.connectedComponentsMap C)) (componentMap_mem e C)
      ((e.contMDiff.comp contMDiff_subtype_val).contMDiffAt)
  contMDiff_invFun := by
    intro y
    exact DifferentialGeometry.codRestr_contMDiffAt (V := M.componentOpen C)
      (componentMap_inv_mem e C) ((e.symm.contMDiff.comp contMDiff_subtype_val).contMDiffAt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent

@[simp] theorem diffeomorphComponent_apply
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    (diffeomorphComponent e C x).val = e x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_apply

@[simp] theorem diffeomorphComponent_symm_apply
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier)
    (y : N.componentOpen (e.continuous.connectedComponentsMap C)) :
    ((diffeomorphComponent e C).symm y).val = e.symm y.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_symm_apply ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_symm_apply

theorem diffeomorphComponent_mfderiv
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (diffeomorphComponent e C) x =
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x.val := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))]
  exact DifferentialGeometry.mfderiv_restrict_open e (M.componentOpen C) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_mfderiv ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.diffeomorphComponent_mfderiv

end DifferentialGeometry.Topology.ClosedOrientedManifold
