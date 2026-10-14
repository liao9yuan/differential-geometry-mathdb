import Submission.DifferentialGeometry.Topology.Homotopy.LoopTopology
import Submission.DifferentialGeometry.Topology.Homotopy.Map

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



def genLoopTargetHomeomorph (e : X ≃ₜ Y) (x : X) : GenLoop N X x ≃ₜ GenLoop N Y (e x) where
  toFun := genLoopPostcompose ⟨e, e.continuous⟩ x
  invFun p := ⟨(⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp p.val,
    fun y hy => by
      change e.symm (p y) = x
      rw [GenLoop.boundary p y hy, e.symm_apply_apply]⟩
  left_inv p := by ext t; exact e.symm_apply_apply (p t)
  right_inv p := by ext t; exact e.apply_symm_apply (p t)
  continuous_toFun := ((_root_.ContinuousMap.continuous_postcomp (⟨e, e.continuous⟩ : C(X, Y))).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((_root_.ContinuousMap.continuous_postcomp (⟨e.symm, e.symm.continuous⟩ : C(Y, X))).comp
    continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTargetHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTargetHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTargetHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopTargetHomeomorph


def homotopyGroupHomeomorphMulEquiv [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e x) where
  toEquiv := Quotient.congr (genLoopTargetHomeomorph e x).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff (genLoopTargetHomeomorph e x) p q).symm)
  map_mul' a b := (homotopyGroupMapHom (N := N) ⟨e, e.continuous⟩ x).map_mul a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupHomeomorphMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupHomeomorphMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupHomeomorphMulEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupHomeomorphMulEquiv

end DifferentialGeometry.Topology
