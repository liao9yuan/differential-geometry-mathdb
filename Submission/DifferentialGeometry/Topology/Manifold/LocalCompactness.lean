import Mathlib.Geometry.Manifold.Metrizable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.Manifold

section ChartedSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M]

theorem regularSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M] : RegularSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : WeaklyLocallyCompactSpace M := inferInstance
  have : R1Space M := T2Space.r1Space
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace

theorem sigmaCompactSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    [SecondCountableTopology M] : SigmaCompactSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace

end ChartedSpaceInstances


end DifferentialGeometry.Topology.Manifold
