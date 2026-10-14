import Mathlib.Topology.Homotopy.HomotopyGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def genLoopPostcompose (f : C(X, Y)) (x : X) (p : GenLoop N X x) : GenLoop N Y (f x) :=
  ⟨f.comp p.val, fun y hy => congrArg f (GenLoop.boundary p y hy)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPostcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPostcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPostcompose ``Submission.DifferentialGeometry.Topology.genLoopPostcompose


theorem genLoopPostcompose_homotopic (f : C(X, Y)) (x : X)
    {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopPostcompose f x p) (genLoopPostcompose f x q) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPostcompose_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPostcompose_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPostcompose_homotopic ``Submission.DifferentialGeometry.Topology.genLoopPostcompose_homotopic


def homotopyGroupMap (f : C(X, Y)) (x : X) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (genLoopPostcompose f x) (fun _ _ h => genLoopPostcompose_homotopic f x h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupMap ``Submission.DifferentialGeometry.Topology.homotopyGroupMap


theorem homotopyGroupMap_id (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupMap (.id X) x a = a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupMap_id ``Submission.DifferentialGeometry.Topology.homotopyGroupMap_id


theorem homotopyGroupMap_comp {Z : Type*} [TopologicalSpace Z]
    (g : C(Y, Z)) (f : C(X, Y)) (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupMap (g.comp f) x a = homotopyGroupMap g (f x) (homotopyGroupMap f x a) := by
  induction a using Quotient.inductionOn with
  | h p => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupMap_comp ``Submission.DifferentialGeometry.Topology.homotopyGroupMap_comp


theorem genLoopPostcompose_transAt [DecidableEq N] (f : C(X, Y)) (x : X)
    (i : N) (p q : GenLoop N X x) :
    genLoopPostcompose f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopPostcompose f x p) (genLoopPostcompose f x q) := by
  apply GenLoop.ext
  intro t
  simp only [genLoopPostcompose, GenLoop.mk_apply, ContinuousMap.comp_apply,
    GenLoop.transAt, GenLoop.coe_coe, GenLoop.coe_copy]
  split_ifs <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPostcompose_transAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPostcompose_transAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPostcompose_transAt ``Submission.DifferentialGeometry.Topology.genLoopPostcompose_transAt


def homotopyGroupMapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := homotopyGroupMap f x
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : N := Classical.arbitrary N
        have hmul := congrArg (homotopyGroupMap (N := N) f x)
          (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        have hconcat := congrArg
          (fun r : GenLoop N Y (f x) => (⟦r⟧ : HomotopyGroup N Y (f x)))
          (genLoopPostcompose_transAt f x i q p)
        exact hconcat.trans (HomotopyGroup.mul_spec (i := i)
          (p := genLoopPostcompose f x p) (q := genLoopPostcompose f x q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupMapHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupMapHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupMapHom ``Submission.DifferentialGeometry.Topology.homotopyGroupMapHom


end DifferentialGeometry.Topology
