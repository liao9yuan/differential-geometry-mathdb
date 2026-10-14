import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronJoinQuotient
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronGenLoop
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronJoinBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.ContinuousMap
open scoped _root_.unitInterval
namespace DifferentialGeometry.Simplex
variable {X : Type*} [TopologicalSpace X] {x : X}

private def genLoopCubeMap (p : GenLoop (Fin 3) X x) : C(I × I × I, X) :=
  ⟨fun q => p ![q.2.2,q.2.1,q.1], by fun_prop⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.genLoopCubeMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.genLoopCubeMap target :: scope.openDecls } }

private theorem genLoopCubeMap_zero (p : GenLoop (Fin 3) X x) (t u v : I) :
    genLoopCubeMap p (0,t,u) = genLoopCubeMap p (0,t,v) := by
  exact (p.property _ ⟨2,Or.inl rfl⟩).trans (p.property _ ⟨2,Or.inl rfl⟩).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.genLoopCubeMap_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.genLoopCubeMap_zero target :: scope.openDecls } }

private theorem genLoopCubeMap_one (p : GenLoop (Fin 3) X x) (t u v : I) :
    genLoopCubeMap p (1,t,u) = genLoopCubeMap p (1,v,u) := by
  exact (p.property _ ⟨2,Or.inr rfl⟩).trans (p.property _ ⟨2,Or.inr rfl⟩).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.genLoopCubeMap_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.genLoopCubeMap_one target :: scope.openDecls } }

def tetrahedronGenLoopRepresentative (p : GenLoop (Fin 3) X x) : C(stdSimplex ℝ (Fin 4), X) :=
  tetrahedronJoinDesc (genLoopCubeMap p) (genLoopCubeMap_zero p) (genLoopCubeMap_one p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative ``Submission.DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative

theorem tetrahedronGenLoopRepresentative_join (p : GenLoop (Fin 3) X x) (q : I × I × I) :
    tetrahedronGenLoopRepresentative p (tetrahedronJoin q) = p ![q.2.2,q.2.1,q.1] :=
  tetrahedronJoinDesc_apply (genLoopCubeMap p) (genLoopCubeMap_zero p) (genLoopCubeMap_one p) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_join then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_join"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_join ``Submission.DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_join

theorem tetrahedronGenLoopRepresentative_boundary (p : GenLoop (Fin 3) X x)
    (q : stdSimplex ℝ (Fin 4)) (hq : q ∈ boundary (Fin 4)) :
    tetrahedronGenLoopRepresentative p q = x := by
  obtain ⟨r, rfl⟩ := tetrahedronJoin_surjective q
  rw [tetrahedronGenLoopRepresentative_join]
  exact p.property _ ((tetrahedronJoin_mem_boundary_iff ![r.2.2,r.2.1,r.1]).mp hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_boundary ``Submission.DifferentialGeometry.Simplex.tetrahedronGenLoopRepresentative_boundary

theorem tetrahedronGenLoop_representative (p : GenLoop (Fin 3) X x) :
    tetrahedronGenLoop (tetrahedronGenLoopRepresentative p) x
      (tetrahedronGenLoopRepresentative_boundary p) = p := by
  ext v
  rw [tetrahedronGenLoop_apply, tetrahedronGenLoopRepresentative_join]
  congr 1
  ext i
  fin_cases i <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronGenLoop_representative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronGenLoop_representative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronGenLoop_representative ``Submission.DifferentialGeometry.Simplex.tetrahedronGenLoop_representative

theorem exists_tetrahedronGenLoop_eq (p : GenLoop (Fin 3) X x) :
    ∃ g : C(stdSimplex ℝ (Fin 4), X), ∃ hg : ∀ q ∈ boundary (Fin 4), g q = x,
      tetrahedronGenLoop g x hg = p :=
  ⟨tetrahedronGenLoopRepresentative p, tetrahedronGenLoopRepresentative_boundary p,
    tetrahedronGenLoop_representative p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_eq ``Submission.DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_eq

theorem exists_tetrahedronGenLoop_class_eq (a : HomotopyGroup (Fin 3) X x) :
    ∃ g : C(stdSimplex ℝ (Fin 4), X), ∃ hg : ∀ q ∈ boundary (Fin 4), g q = x,
      (⟦tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨g,hg,hp⟩ := exists_tetrahedronGenLoop_eq p
    exact ⟨g,hg,congrArg (fun q : GenLoop (Fin 3) X x => (⟦q⟧ : HomotopyGroup (Fin 3) X x)) hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_class_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_class_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_class_eq ``Submission.DifferentialGeometry.Simplex.exists_tetrahedronGenLoop_class_eq

end DifferentialGeometry.Simplex
