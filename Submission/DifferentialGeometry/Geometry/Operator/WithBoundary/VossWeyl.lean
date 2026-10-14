import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Laplacian
import Submission.DifferentialGeometry.Tensor.Coordinates.PartialDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Operator.WithBoundary

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartCoeff_grad_g_with_boundary_eq_gradChartCoeff
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    {x : M} (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    chartCoeff (I := I) α (gradGWithBoundarySection (I := I) g hf hf_int) i x =
      gradChartCoeff (I := I) g α f i x := by
  exact chartBasisFamily_repr_gradFun (I := I) g α
    (hf.mdifferentiable (by simp) x) hx hx_int i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.chartCoeff_grad_g_with_boundary_eq_gradChartCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.chartCoeff_grad_g_with_boundary_eq_gradChartCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.chartCoeff_grad_g_with_boundary_eq_gradChartCoeff ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.chartCoeff_grad_g_with_boundary_eq_gradChartCoeff

private theorem chartCoeffOnE_grad_g_with_boundary_eq_gradChartCoeffOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (gradGWithBoundarySection (I := I) g hf hf_int) i y =
      gradChartCoeffOnE (I := I) g α f i y := by
  have hys := (extChartAt I α).map_target (interior_subset hy)
  have hb : (extChartAt I α).symm y ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact hys
  have hright := (extChartAt I α).right_inv (interior_subset hy)
  have hc := chartCoeff_grad_g_with_boundary_eq_gradChartCoeff g α hf hf_int hb
    (hright.symm ▸ hy) i
  unfold chartCoeffOnE
  rw [hc]
  simp only [gradChartCoeff, gradChartCoeffOnE, chartInvGramOnE, hright]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.chartCoeffOnE_grad_g_with_boundary_eq_gradChartCoeffOnE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.WithBoundary.chartCoeffOnE_grad_g_with_boundary_eq_gradChartCoeffOnE target :: scope.openDecls } }

theorem voss_weyl_laplacian_with_boundary_formula
    [T2Space M] (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    {x : M} (hx : x ∈ (chartAt H α).source) (hx_int : x ∈ I.interior M) :
    ΔGWithBoundary (I := I) g hf hf_int x =
      chartVossWeylLaplacian (I := I) g α f x := by
  rw [Δ_g_with_boundary_def,
    voss_weyl_divergence_with_boundary_formula (I := I) g α
      (gradGWithBoundarySection (I := I) g hf hf_int) hx,
    localDivergenceWithin_eq_localDivergence_of_isInteriorPoint (I := I) g α
      (gradGWithBoundarySection (I := I) g hf hf_int) hx hx_int,
    localDivergence_def, chartVossWeylLaplacian_def]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hnhds : interior (extChartAt I α).target ∈ 𝓝 (extChartAt I α x) :=
    isOpen_interior.mem_nhds
      (extChartAt_mem_interior_target_of_isInteriorPoint (I := I) α hx hx_int)
  have heq : (fun y : E => chartCoeffOnE (I := I) α
      (gradGWithBoundarySection (I := I) g hf hf_int) i y * chartDensityOnE (I := I) g α y)
      =ᶠ[𝓝 (extChartAt I α x)] chartVossWeylIntegrand (I := I) g α f i := by
    filter_upwards [hnhds] with y hy
    rw [chartCoeffOnE_grad_g_with_boundary_eq_gradChartCoeffOnE g α hf hf_int i hy]
    rfl
  unfold partialDeriv
  rw [heq.fderiv_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.WithBoundary.voss_weyl_laplacian_with_boundary_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.WithBoundary.voss_weyl_laplacian_with_boundary_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.WithBoundary.voss_weyl_laplacian_with_boundary_formula ``Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.voss_weyl_laplacian_with_boundary_formula

end DifferentialGeometry.Geometry.Operator.WithBoundary
