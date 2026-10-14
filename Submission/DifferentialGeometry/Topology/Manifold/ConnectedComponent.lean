import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Connected.LocallyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def connectedComponentOpen (p : M) : _root_.TopologicalSpace.Opens M := by
  letI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  exact ⟨connectedComponent p, isOpen_connectedComponent⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.connectedComponentOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.connectedComponentOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.connectedComponentOpen ``Submission.DifferentialGeometry.connectedComponentOpen

def connectedComponentPoint (p : M) : connectedComponentOpen (I := I) p :=
  ⟨p, mem_connectedComponent⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.connectedComponentPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.connectedComponentPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.connectedComponentPoint ``Submission.DifferentialGeometry.connectedComponentPoint

theorem connectedComponentOpen_connectedSpace (p : M) :
    ConnectedSpace (connectedComponentOpen (I := I) p) := by
  apply Subtype.connectedSpace
  unfold connectedComponentOpen
  exact isConnected_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.connectedComponentOpen_connectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.connectedComponentOpen_connectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.connectedComponentOpen_connectedSpace ``Submission.DifferentialGeometry.connectedComponentOpen_connectedSpace

theorem connectedComponentOpen_compactSpace [CompactSpace M] (p : M) :
    CompactSpace (connectedComponentOpen (I := I) p) := by
  apply isCompact_iff_compactSpace.mp
  unfold connectedComponentOpen
  exact (isClosed_connectedComponent (x := p)).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.connectedComponentOpen_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.connectedComponentOpen_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.connectedComponentOpen_compactSpace ``Submission.DifferentialGeometry.connectedComponentOpen_compactSpace

end DifferentialGeometry
