import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedCellCoefficients
import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.GramDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Matrix _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Handle
open _root_.Submission.DifferentialGeometry.Topology.Manifold

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell target :: scope.openDecls } }

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instT2SpaceEuclideanSpaceRealFinHAddNatOfNat_differentialGeometry : T2Space V := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instT2SpaceEuclideanSpaceRealFinHAddNatOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instT2SpaceEuclideanSpaceRealFinHAddNatOfNat_differentialGeometry target :: scope.openDecls } }

theorem densityOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) {y : W}
    (hα : ‖α.val‖ < 1)
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) :
    densityOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α y =
      Real.sqrt (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))).det := by
  have hgram :
      (Matrix.of (fun k l => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y)) =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))) := by
    funext k l
    exact gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy k l
  rw [densityOnEuclid_eq_sqrt_det, hgram]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_closedCellPullbackMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_closedCellPullbackMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_closedCellPullbackMetricFamily ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_closedCellPullbackMetricFamily

theorem invGramOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) {y : W}
    (hα : ‖α.val‖ < 1)
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    invGramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)))⁻¹ i j := by
  have hgram :
      (Matrix.of (fun k l => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y)) =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))) := by
    funext k l
    exact gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy k l
  rw [invGramOnEuclid_eq_matrix_inv, hgram]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_closedCellPullbackMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_closedCellPullbackMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_closedCellPullbackMetricFamily ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_closedCellPullbackMetricFamily

theorem weightedInvGramOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) {y : W}
    (hα : ‖α.val‖ < 1)
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    weightedInvGramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      Real.sqrt (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))).det *
        (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)))⁻¹ i j := by
  have hgram :
      (Matrix.of (fun k l => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y)) =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))) := by
    funext k l
    exact gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy k l
  rw [weightedInvGramOnEuclid_eq_sqrt_det_mul_inv, hgram]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_closedCellPullbackMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_closedCellPullbackMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_closedCellPullbackMetricFamily ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_closedCellPullbackMetricFamily

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
