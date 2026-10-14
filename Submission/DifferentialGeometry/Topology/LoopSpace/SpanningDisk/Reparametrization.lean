import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

theorem diskTrace_comp_of_map_boundary {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (φ : C(closedDisk, closedDisk)) (δ : C(loopCircle, loopCircle))
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) :
    diskTrace (u.comp φ) = (diskTrace u).comp δ := by
  ext θ
  exact congrArg u (hboundary θ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskTrace_comp_of_map_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskTrace_comp_of_map_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskTrace_comp_of_map_boundary ``Submission.DifferentialGeometry.Topology.diskTrace_comp_of_map_boundary

end DifferentialGeometry.Topology

end
