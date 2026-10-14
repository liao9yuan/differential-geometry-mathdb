import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [CompleteSpace E] [ConnectedSpace M] in
theorem intrinsicFramedExp_image_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) {r : ℝ} :
    intrinsicFramedExp g hEnorm p '' Metric.ball (0 : E) r =
      Metric.eball p (ENNReal.ofReal r) := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact intrinsicFrame_mem_eball g hEnorm p (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  · intro hq
    have hq' : _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal r := by
      rw [← IsRiemannianManifold.out (I := I)]
      exact Metric.mem_eball'.mp hq
    obtain ⟨v, hv, hvnorm⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      g hEnorm p q (ne_of_lt (hq'.trans ENNReal.ofReal_lt_top))
    let w : E := (normalFrame (I := I) g p).symm v
    have hw : ‖w‖ = (_root_.Manifold.riemannianEDist I p q).toReal := by
      rw [← normalFrame_sqrt (I := I) g p w]
      dsimp [w]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hvnorm
    refine ⟨w, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hw]
      exact ENNReal.toReal_lt_of_lt_ofReal hq'
    · have h := intrinsicFrame_apply (I := I) g hEnorm p w
      have hn : normalFrame (I := I) g p w = v :=
        ContinuousLinearEquiv.apply_symm_apply _ _
      exact h.trans ((congrArg (expMapIntrinsic (I := I) g hEnorm p) hn).trans hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicFramedExp_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicFramedExp_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicFramedExp_image_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.intrinsicFramedExp_image_ball

omit [CompleteSpace E] [ConnectedSpace M] in
theorem IntrinsicBallChart.image_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M)
    {r R : ℝ} (c : IntrinsicBallChart g hEnorm p R) (hrR : r ≤ R) :
    c.hom '' Metric.ball (0 : E) r = Metric.eball p (ENNReal.ofReal r) := by
  rw [← intrinsicFramedExp_image_ball g hEnorm p]
  exact _root_.Set.image_congr (fun z hz => c.hom_eq (Metric.ball_subset_ball hrR hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.image_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.image_ball

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end
