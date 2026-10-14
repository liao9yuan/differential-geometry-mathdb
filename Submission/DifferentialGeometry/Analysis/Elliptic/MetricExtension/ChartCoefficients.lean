import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.PullbackGram
import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.GramDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Matrix

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open _root_.Submission.DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem gramOnEuclid_eq_pullbackMetricCoefficients
    (g : SmoothRiemannianMetric I M) (α : M) {y : EuclN}
    (hy : y ∈ interior (chartTargetEuclid (I := I) α))
    (i j : Fin (Module.finrank ℝ E)) :
    gramOnEuclid g α i j y =
      pullbackMetricCoefficients g
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have himm : ∀ x : M, Function.Injective (mfderiv I I (@id M) x) := by
    intro x
    rw [mfderiv_id]
    exact Function.injective_id
  have hg : g.pullback id contMDiff_id himm = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [SmoothRiemannianMetric.pullback_inner, mfderiv_id,
      ContinuousLinearMap.id_apply, id_eq]
  have hset : toEuclidean (E := E) '' interior (extChartAt I α).target =
      interior (chartTargetEuclid (I := I) α) :=
    (toEuclidean (E := E)).toHomeomorph.image_interior (extChartAt I α).target
  rw [← hset] at hy
  simpa only [hg, id_eq] using gramOnEuclid_pullback g id contMDiff_id himm α hy i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_eq_pullbackMetricCoefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_eq_pullbackMetricCoefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_eq_pullbackMetricCoefficients ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_eq_pullbackMetricCoefficients

private theorem gramMatrixOnEuclid_eq_pullbackMetricCoefficients
    (g : SmoothRiemannianMetric I M) (α : M) {y : EuclN}
    (hy : y ∈ interior (chartTargetEuclid (I := I) α)) :
    Matrix.of (fun i j => gramOnEuclid g α i j y) =
      Matrix.of (fun i j => pullbackMetricCoefficients g
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  funext i j
  exact gramOnEuclid_eq_pullbackMetricCoefficients g α hy i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramMatrixOnEuclid_eq_pullbackMetricCoefficients
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramMatrixOnEuclid_eq_pullbackMetricCoefficients target :: scope.openDecls } }

theorem densityOnEuclid_eq_sqrt_det_pullbackMetricCoefficients
    (g : SmoothRiemannianMetric I M) (α : M) {y : EuclN}
    (hy : y ∈ interior (chartTargetEuclid (I := I) α)) :
    densityOnEuclid g α y =
      Real.sqrt (Matrix.of (fun i j => pullbackMetricCoefficients g
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))).det := by
  rw [densityOnEuclid_eq_sqrt_det, gramMatrixOnEuclid_eq_pullbackMetricCoefficients g α hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det_pullbackMetricCoefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det_pullbackMetricCoefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det_pullbackMetricCoefficients ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det_pullbackMetricCoefficients

theorem invGramOnEuclid_eq_inv_pullbackMetricCoefficients
    (g : SmoothRiemannianMetric I M) (α : M) {y : EuclN}
    (hy : y ∈ interior (chartTargetEuclid (I := I) α))
    (i j : Fin (Module.finrank ℝ E)) :
    invGramOnEuclid g α i j y =
      (Matrix.of (fun k l => pullbackMetricCoefficients g
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)))⁻¹ i j := by
  rw [invGramOnEuclid_eq_matrix_inv, gramMatrixOnEuclid_eq_pullbackMetricCoefficients g α hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_inv_pullbackMetricCoefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_inv_pullbackMetricCoefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_inv_pullbackMetricCoefficients ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_inv_pullbackMetricCoefficients

theorem weightedInvGramOnEuclid_eq_sqrt_det_mul_inv_pullbackMetricCoefficients
    (g : SmoothRiemannianMetric I M) (α : M) {y : EuclN}
    (hy : y ∈ interior (chartTargetEuclid (I := I) α))
    (i j : Fin (Module.finrank ℝ E)) :
    weightedInvGramOnEuclid g α i j y =
      Real.sqrt (Matrix.of (fun k l => pullbackMetricCoefficients g
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))).det *
      (Matrix.of (fun k l => pullbackMetricCoefficients g
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)))⁻¹ i j := by
  rw [weightedInvGramOnEuclid_eq_sqrt_det_mul_inv,
    gramMatrixOnEuclid_eq_pullbackMetricCoefficients g α hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv_pullbackMetricCoefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv_pullbackMetricCoefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv_pullbackMetricCoefficients ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv_pullbackMetricCoefficients

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
