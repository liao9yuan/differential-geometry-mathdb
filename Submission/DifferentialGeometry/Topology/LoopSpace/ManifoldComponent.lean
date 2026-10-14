import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








namespace DifferentialGeometry.Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



def loopComponentOpen (γ : freeLoop M) : TopologicalSpace.Opens M := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  exact ⟨loopComponent γ, isOpen_loopComponent γ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopComponentOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopComponentOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopComponentOpen ``Submission.DifferentialGeometry.Topology.loopComponentOpen

@[simp] theorem loopComponentOpen_coe (γ : freeLoop M) :
    (loopComponentOpen E γ : Set M) = loopComponent γ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopComponentOpen_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopComponentOpen_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopComponentOpen_coe ``Submission.DifferentialGeometry.Topology.loopComponentOpen_coe

theorem isClosed_loopComponentOpen (γ : freeLoop M) :
    IsClosed (loopComponentOpen E γ : Set M) := isClosed_loopComponent γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosed_loopComponentOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosed_loopComponentOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosed_loopComponentOpen ``Submission.DifferentialGeometry.Topology.isClosed_loopComponentOpen

instance loopComponentOpen_connectedSpace (γ : freeLoop M) :
    ConnectedSpace (loopComponentOpen E γ) :=
  inferInstanceAs (ConnectedSpace (loopComponent γ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopComponentOpen_connectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopComponentOpen_connectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopComponentOpen_connectedSpace ``Submission.DifferentialGeometry.Topology.loopComponentOpen_connectedSpace

instance loopComponentOpen_compactSpace [CompactSpace M] (γ : freeLoop M) :
    CompactSpace (loopComponentOpen E γ) :=
  inferInstanceAs (CompactSpace (loopComponent γ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopComponentOpen_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopComponentOpen_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopComponentOpen_compactSpace ``Submission.DifferentialGeometry.Topology.loopComponentOpen_compactSpace

end DifferentialGeometry.Topology
