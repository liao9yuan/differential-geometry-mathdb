import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurck.Existence
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.Cm
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem c1_norm_time_continuous_from_h1_time_derivative
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T) := by
  obtain ⟨_hT, _hinit, hderiv⟩ := _hsol
  intro x v w t ht
  have hcont_within_Ici :
      ContinuousWithinAt (fun s : ℝ => (g_DT s).inner x v w) (Set.Ici (0 : ℝ)) t :=
    (hderiv t ht x v w).continuousWithinAt
  exact hcont_within_Ici.mono Set.Ico_subset_Ici_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.c1_norm_time_continuous_from_h1_time_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.c1_norm_time_continuous_from_h1_time_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.c1_norm_time_continuous_from_h1_time_derivative ``Submission.DifferentialGeometry.PDE.RicciFlow.c1_norm_time_continuous_from_h1_time_derivative
end DifferentialGeometry.PDE.RicciFlow
