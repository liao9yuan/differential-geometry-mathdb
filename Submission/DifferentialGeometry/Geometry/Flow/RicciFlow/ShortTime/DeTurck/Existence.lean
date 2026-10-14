import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.StrictParabolicity
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Smoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.ConnectionLaplacianMaximalRegularity
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.PointwiseDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurck.InitialData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]
omit [SigmaCompactSpace M] in
theorem deTurckRicci_shortTime_existence_of_closed
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := by
  obtain ⟨T, g_DT, hbundle⟩ :=
    deturck_ricci_flow_parabolic_short_time_existence (I := I) g₀ g_bg
  exact ⟨T, g_DT, hbundle.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRicci_shortTime_existence_of_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRicci_shortTime_existence_of_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRicci_shortTime_existence_of_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRicci_shortTime_existence_of_closed

end DifferentialGeometry.PDE.RicciFlow
