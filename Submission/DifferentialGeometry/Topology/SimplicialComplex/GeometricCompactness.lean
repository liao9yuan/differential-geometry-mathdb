import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.SimplicialComplex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem isCompact_geometricSpace (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    IsCompact K.space :=
  (Set.toFinite K.faces).isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace ``Submission.DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace


instance compactSpace_geometricSpace (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_geometricSpace K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.compactSpace_geometricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.compactSpace_geometricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.compactSpace_geometricSpace ``Submission.DifferentialGeometry.Topology.SimplicialComplex.compactSpace_geometricSpace

end DifferentialGeometry.Topology.SimplicialComplex
