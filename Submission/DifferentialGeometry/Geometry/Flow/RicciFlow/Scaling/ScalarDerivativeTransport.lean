import Submission.DifferentialGeometry.Analysis.ODE.QuadraticBackwardBound
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem SolutionOn.abs_derivWithin_scalar_le_of_parabolic_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gflow : ℝ → SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi) {T Q a b s C : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ u ∈ _root_.Set.Icc a b, S.base.metric u =
      localPullMetric (scaleMetric Q hQ (gflow (T + u / Q))) Phi hPhi)
    (hcarrier : _root_.Set.Icc a b ⊆ D.carrier) (hs : s ∈ _root_.Set.Ioc a b) (x : M)
    (hbound : |derivWithin (fun u => S.scalar u x) (_root_.Set.Iic s) s| ≤ C * S.scalar s x ^ 2) :
    |derivWithin (fun t => metricScalarAt (gflow t) (Phi x))
        (_root_.Set.Iic (T + s / Q)) (T + s / Q)| ≤
      C * metricScalarAt (gflow (T + s / Q)) (Phi x) ^ 2 := by
  have hscalar : _root_.Set.EqOn (fun u => S.scalar u x)
      (fun u => Q⁻¹ * metricScalarAt (gflow (T + u / Q)) (Phi x)) (_root_.Set.Icc a b) := by
    intro u hu
    change metricScalarAt (S.base.metric u) x = Q⁻¹ * metricScalarAt (gflow (T + u / Q)) (Phi x)
    rw [hmetric u hu, metricScalarAt_localPull, metricScalarAt_scaleMetric]
  have hf := Analysis.differentiableWithinAt_of_eqOn_comp_affine_Icc
    (f := fun t => metricScalarAt (gflow t) (Phi x)) (T := T) hQ
    (hS.scalarTime (show s ∈ _root_.Set.Icc a b from ⟨hs.1.le, hs.2⟩) hcarrier x) hscalar hs
  exact (Analysis.abs_derivWithin_le_sq_iff_of_eqOn_comp_affine_Icc hQ hf hscalar hs).mpr hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.abs_derivWithin_scalar_le_of_parabolic_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.abs_derivWithin_scalar_le_of_parabolic_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.abs_derivWithin_scalar_le_of_parabolic_localPullMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.abs_derivWithin_scalar_le_of_parabolic_localPullMetric

end DifferentialGeometry.PDE.RicciFlow
