import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Submission.DifferentialGeometry.Analysis.Integration.Measure.ModelChange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem normalizedShrinkerMass_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (f : M → ℝ) :
    normalizedShrinkerMass (g.transContinuousLinearEquiv e) f = normalizedShrinkerMass g f := by
  unfold normalizedShrinkerMass
  rw [← e.toLinearEquiv.finrank_eq,
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_transContinuousLinearEquiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_transContinuousLinearEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_transContinuousLinearEquiv

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
