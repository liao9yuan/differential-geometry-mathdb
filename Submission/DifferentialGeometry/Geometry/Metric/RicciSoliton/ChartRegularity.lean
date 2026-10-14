import Submission.DifferentialGeometry.Analysis.Calculus.ContDiff.AffineHessian
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contDiffOn_of_chart_ricci_soliton_equation
    (g : SmoothRiemannianMetric I M) (α : M) (sigma : ℝ)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I α).target)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U)
    (hdu : DifferentiableOn ℝ (fderiv ℝ u) U)
    (heq : ∀ y ∈ U, ∀ i j : Fin (Module.finrank ℝ E),
      fderiv ℝ (fderiv ℝ u) y (chartModelBasis E i) (chartModelBasis E j) =
        (sigma / 2) * chartGramOnE g α i j y - chartRicciTensor g α i j y +
          ∑ k, chartChristoffel g α i j k y * fderiv ℝ u y (chartModelBasis E k)) :
    ContDiffOn ℝ ∞ u U := by
  have hUi : U ⊆ interior (extChartAt I α).target := interior_maximal hUt hU
  apply DifferentialGeometry.Analysis.Calculus.contDiffOn_of_affine_hessian_components
    (chartModelBasis E) hU hu hdu
    (A := fun i j y => (sigma / 2) * chartGramOnE g α i j y -
      chartRicciTensor g α i j y)
    (Γ := fun i j k y => chartChristoffel g α i j k y)
  · intro i j
    exact (contDiffOn_const.mul ((chartGramOnE_contDiffOn g α i j).mono hUt)).sub
      ((chartRicciTensor_contDiffOn_interior g α i j).mono hUi)
  · intro i j k
    exact (chartChristoffel_contDiffOn_interior g α i j k).mono hUi
  · exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_of_chart_ricci_soliton_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_of_chart_ricci_soliton_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_of_chart_ricci_soliton_equation ``Submission.DifferentialGeometry.Geometry.contDiffOn_of_chart_ricci_soliton_equation

theorem contDiffOn_of_intrinsic_ricci_soliton_chart_equation
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) (sigma : ℝ)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I α).target)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U)
    (hdu : DifferentiableOn ℝ (fderiv ℝ u) U)
    (heq : ∀ y ∈ U, ∀ i j : Fin (Module.finrank ℝ E),
      fderiv ℝ (fderiv ℝ u) y (chartModelBasis E i) (chartModelBasis E j) =
        (sigma / 2) * g.inner ((extChartAt I α).symm y)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)) -
        ricciTensor g ((extChartAt I α).symm y)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)) +
        ∑ k, chartChristoffel g α i j k y * fderiv ℝ u y (chartModelBasis E k)) :
    ContDiffOn ℝ ∞ u U := by
  apply contDiffOn_of_chart_ricci_soliton_equation g α sigma hU hUt hu hdu
  intro y hy i j
  have hgood : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact (extChartAt I α).map_target (hUt hy)
  have h := heq y hy i j
  rw [ricciTensor_chartBasisVec_alpha_eq g α i j hgood,
    (extChartAt I α).right_inv (hUt hy)] at h
  simpa only [chartGramOnE_def, chartGramMatrix_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_of_intrinsic_ricci_soliton_chart_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_of_intrinsic_ricci_soliton_chart_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_of_intrinsic_ricci_soliton_chart_equation ``Submission.DifferentialGeometry.Geometry.contDiffOn_of_intrinsic_ricci_soliton_chart_equation

end DifferentialGeometry.Geometry
