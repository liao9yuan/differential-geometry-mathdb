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

variable {X : Type*} [TopologicalSpace X]



def genLoopPathHomeomorph (N : Type*) [Unique N] (x : X) :
    GenLoop N X x ≃ₜ Path x x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_pi fun _ => continuous_snd))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      (continuous_fst.prodMk ((continuous_apply _root_.Inhabited.default).comp continuous_snd))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPathHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPathHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPathHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopPathHomeomorph


theorem genLoopPathHomeomorph_const (N : Type*) [Unique N] (x : X) :
    genLoopPathHomeomorph N x GenLoop.const = Path.refl x := by
  ext t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopPathHomeomorph_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopPathHomeomorph_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopPathHomeomorph_const ``Submission.DifferentialGeometry.Topology.genLoopPathHomeomorph_const

end DifferentialGeometry.Topology
