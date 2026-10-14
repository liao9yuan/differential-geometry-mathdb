import Submission.DifferentialGeometry.Topology.LoopSpace.Family

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

namespace DifferentialGeometry.Topology


def familySphereBasepoint : familySphere :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.familySphereBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.familySphereBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.familySphereBasepoint ``Submission.DifferentialGeometry.Topology.familySphereBasepoint

instance familySphere_nonempty : Nonempty familySphere := ⟨familySphereBasepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.familySphere_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.familySphere_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.familySphere_nonempty ``Submission.DifferentialGeometry.Topology.familySphere_nonempty

end DifferentialGeometry.Topology
