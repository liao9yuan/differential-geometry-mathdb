import Submission.DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem chartCoord_source_mfderiv {U : V → M} {z : V}
    (hU : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) U z) (p : M)
    (hp : U z ∈ (chartAt E p).source) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)).comp
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) U z) =
      fderiv ℝ ((extChartAt 𝓘(ℝ, E) p) ∘ U) z := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp,
    ← mfderiv_comp z (mdifferentiableAt_extChartAt hp) hU, mfderiv_eq_fderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.chartCoord_source_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.chartCoord_source_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.chartCoord_source_mfderiv ``Submission.DifferentialGeometry.Geometry.chartCoord_source_mfderiv

end DifferentialGeometry.Geometry
