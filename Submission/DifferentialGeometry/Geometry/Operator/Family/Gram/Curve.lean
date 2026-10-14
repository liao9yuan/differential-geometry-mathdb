import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Basic
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

theorem chartGramOp_inner_deriv
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    {gamma : ℝ → M} {r : ℝ} (p : M) (t : ℝ)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r)
    (hsrc : gamma r ∈ (chartAt H p).source) :
    _root_.Inner.inner ℝ (chartGramOp G p (t, extChartAt I p (gamma r))
      (deriv ((extChartAt I p) ∘ gamma) r))
      (deriv ((extChartAt I p) ∘ gamma) r) =
      (G.metric t).inner (gamma r)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ)) := by
  rw [chartGramOp_inner, (extChartAt I p).left_inv (by
    simpa only [extChartAt_source] using hsrc)]
  rw [raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt hgamma p hsrc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartGramOp_inner_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartGramOp_inner_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartGramOp_inner_deriv ``Submission.DifferentialGeometry.Geometry.Curvature.chartGramOp_inner_deriv

end DifferentialGeometry.Geometry.Curvature
