import Submission.DifferentialGeometry.Geometry.Operator.Gradient.QuadraticForm
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Analysis.Calculus.FDeriv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normGradSqFun_eq_chartGradientBilin_comp_inl
    (g : SmoothRiemannianMetric I M) {f : M → ℝ → ℝ} {alpha x : M} {t : ℝ}
    (hx : x ∈ (chartAt H alpha).source)
    (hjoint : DifferentiableAt ℝ
      (fun z : E × ℝ => f ((extChartAt I alpha).symm z.1) z.2)
      (extChartAt I alpha x, t)) :
    normGradSqFun g (fun y => f y t) x =
      chartGradientBilin g alpha x
        ((fderiv ℝ (fun z : E × ℝ => f ((extChartAt I alpha).symm z.1) z.2)
          (extChartAt I alpha x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
        ((fderiv ℝ (fun z : E × ℝ => f ((extChartAt I alpha).symm z.1) z.2)
          (extChartAt I alpha x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) := by
  have hspatial := hjoint.hasFDerivAt.comp (extChartAt I alpha x)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (extChartAt I alpha x) t)
  have hslice : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y t) x := by
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := I) (I' := 𝓘(ℝ, ℝ)) (x := alpha) (x' := x) hx).mpr
    exact hspatial.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  rw [normGradSqFun_def, grad_norm_sq_eq_chartGradientBilin g alpha hslice hx]
  have hderiv :
      fderiv ℝ (Tensor.Coordinates.scalarOnE (I := I) alpha (fun y => f y t))
        (extChartAt I alpha x) =
      (fderiv ℝ (fun z : E × ℝ => f ((extChartAt I alpha).symm z.1) z.2)
        (extChartAt I alpha x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    exact hspatial.fderiv
  rw [hderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartGradientBilin_comp_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartGradientBilin_comp_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartGradientBilin_comp_inl ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_chartGradientBilin_comp_inl

end DifferentialGeometry.Geometry.Operator
