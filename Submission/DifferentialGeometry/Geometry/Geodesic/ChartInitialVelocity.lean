import Submission.DifferentialGeometry.Geometry.Geodesic.Local
import Submission.DifferentialGeometry.Geometry.Geodesic.Local.Existence
import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_geodesic_with_initial_chart_velocity_at
    (g : SmoothRiemannianMetric I M) (p q : M)
    (hq : q ∈ (chartAt H p).source) (w : E) :
    ∃ γ : ℝ → M, γ 0 = q ∧ IsGeodesicAt (I := I) g γ 0 ∧
      deriv ((extChartAt I p) ∘ γ) 0 = w := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let v : TangentSpace I q := (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).symmL ℝ q w
  obtain ⟨γ, f, hfzero, hγf, hγzero, hf, hγ⟩ :=
    exists_geodesic_with_initial_velocity_at g q v
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : E) = v := by
    have hh := IsMIntegralCurveAt.mfderiv_proj_one hf (by rw [hfzero]; exact mem_chart_source H q)
    rw [hγf]
    exact hh.trans (congrArg (fun z : TangentBundle I M => (z.snd : E)) hfzero)
  refine ⟨γ, hγzero, hγ, ?_⟩
  have hrep := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    ((DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hγ).mdifferentiableAt
      (by simp)) p (by rwa [hγzero])
  change (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ 0)
    (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) = deriv ((extChartAt I p) ∘ γ) 0 at hrep
  rw [hvel, hγzero] at hrep
  have hbase : q ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hq
  exact hrep.symm.trans
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt_symmL
      (R := ℝ) hbase w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_chart_velocity_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_chart_velocity_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_chart_velocity_at ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_chart_velocity_at

end DifferentialGeometry.Geometry.Riemannian.Geodesic
