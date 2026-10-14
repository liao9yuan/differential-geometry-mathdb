import Submission.DifferentialGeometry.Topology.Homotopy.CubeBoundaryRelation
import Submission.DifferentialGeometry.Topology.Homotopy.Adjunction
import Submission.DifferentialGeometry.Topology.Homotopy.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap
open scoped _root_.unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

private def homotopyGroupLoopTwoMulEquiv :
    HomotopyGroup (Fin 2) (GenLoop (Fin 1) X x) GenLoop.const ≃*
      HomotopyGroup (Fin 3) X x :=
  (homotopyGroupIteratedLoopMulEquiv (K := Fin 2) (N := Fin 1) x).trans
    (homotopyGroupReindexMulEquiv finSumFinEquiv x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homotopyGroupLoopTwoMulEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homotopyGroupLoopTwoMulEquiv target :: scope.openDecls } }

def cubeBoundaryLoopFace (G : C(I × I × I, GenLoop (Fin 1) X x))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = GenLoop.const)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : GenLoop (Fin 3) X x :=
  GenLoop.congr x finSumFinEquiv
    (GenLoop.genLoopGenLoopEquiv x (cubeBoundaryFace G hG j e he))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeBoundaryLoopFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeBoundaryLoopFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeBoundaryLoopFace ``Submission.DifferentialGeometry.Topology.cubeBoundaryLoopFace

theorem cubeBoundaryLoopFace_apply (G : C(I × I × I, GenLoop (Fin 1) X x))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = GenLoop.const)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) (v : Fin 3 → I) :
    cubeBoundaryLoopFace G hG j e he v =
      G (match j with
        | 0 => (e, v 1, v 0)
        | 1 => (v 1, e, v 0)
        | 2 => (v 1, v 0, e)) (fun _ => v 2) := by
  fin_cases j <;>
    change G _ (fun k => v (finSumFinEquiv (Sum.inr k))) = _ <;>
    congr 1 <;> funext k <;> fin_cases k <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeBoundaryLoopFace_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeBoundaryLoopFace_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeBoundaryLoopFace_apply ``Submission.DifferentialGeometry.Topology.cubeBoundaryLoopFace_apply

theorem homotopyGroup_loop_cube_boundary_relation
    (G : C(I × I × I, GenLoop (Fin 1) X x))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = GenLoop.const) :
    let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : HomotopyGroup (Fin 3) X x :=
      ⟦cubeBoundaryLoopFace G hG i e he⟧
    q 0 1 (Or.inr rfl) * q 1 0 (Or.inl rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) := by
  let E := homotopyGroupLoopTwoMulEquiv (x := x)
  let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) :
      HomotopyGroup (Fin 2) (GenLoop (Fin 1) X x) GenLoop.const :=
    ⟦cubeBoundaryFace G hG i e he⟧
  have h : q 0 1 (Or.inr rfl) * q 1 0 (Or.inl rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) :=
    homotopyGroup_cube_boundary_relation G hG
  have h' := congrArg E h
  rw [map_mul, map_mul, map_mul, map_mul] at h'
  exact h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroup_loop_cube_boundary_relation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroup_loop_cube_boundary_relation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroup_loop_cube_boundary_relation ``Submission.DifferentialGeometry.Topology.homotopyGroup_loop_cube_boundary_relation

end DifferentialGeometry.Topology
