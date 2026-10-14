import Submission.DifferentialGeometry.Topology.Homotopy.Homeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def genLoopBasedMap (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y)
    (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.val, fun t ht => (congrArg f (GenLoop.boundary p t ht)).trans hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopBasedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopBasedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopBasedMap ``Submission.DifferentialGeometry.Topology.genLoopBasedMap


def homotopyGroupBasedMap (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (genLoopBasedMap f x y hf)
    (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupBasedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupBasedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupBasedMap ``Submission.DifferentialGeometry.Topology.homotopyGroupBasedMap


def homotopyGroupBasedMapHom [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := homotopyGroupBasedMap f x y hf
  map_one' := by
    subst y
    exact (homotopyGroupMapHom f x).map_one
  map_mul' a b := by
    subst y
    exact (homotopyGroupMapHom f x).map_mul a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupBasedMapHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupBasedMapHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupBasedMapHom ``Submission.DifferentialGeometry.Topology.homotopyGroupBasedMapHom



def genLoopBasedHomeomorph (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) :
    GenLoop N X x ≃ₜ GenLoop N Y y where
  toFun := genLoopBasedMap ⟨e, e.continuous⟩ x y he
  invFun := genLoopBasedMap ⟨e.symm, e.symm.continuous⟩ y x
    ((congrArg e.symm he).symm.trans (e.symm_apply_apply x))
  left_inv p := by ext t; exact e.symm_apply_apply (p t)
  right_inv p := by ext t; exact e.apply_symm_apply (p t)
  continuous_toFun := ((_root_.ContinuousMap.continuous_postcomp (⟨e, e.continuous⟩ : C(X, Y))).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((_root_.ContinuousMap.continuous_postcomp (⟨e.symm, e.symm.continuous⟩ : C(Y, X))).comp
    continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopBasedHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopBasedHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopBasedHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopBasedHomeomorph


def homotopyGroupBasedHomeomorphMulEquiv [DecidableEq N] [Nonempty N]
    (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y where
  toEquiv := Quotient.congr (genLoopBasedHomeomorph e x y he).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff (genLoopBasedHomeomorph e x y he) p q).symm)
  map_mul' a b := (homotopyGroupBasedMapHom ⟨e, e.continuous⟩ x y he).map_mul a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupBasedHomeomorphMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupBasedHomeomorphMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupBasedHomeomorphMulEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupBasedHomeomorphMulEquiv

end DifferentialGeometry.Topology
