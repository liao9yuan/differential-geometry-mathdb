import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall.Coordinates
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Chart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Handle

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local instance _root_.Submission.DifferentialGeometry.Tensor.Coordinates.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell ``Submission.DifferentialGeometry.Tensor.Coordinates.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
local instance _root_.Submission.DifferentialGeometry.Tensor.Coordinates.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell ``Submission.DifferentialGeometry.Tensor.Coordinates.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell

private theorem closedCell_chart_eq {x y : ClosedCell (m + 1)}
    (hx : ‖x.val‖ < 1) (hy : ‖y.val‖ < 1) :
    chartAt (EuclideanHalfSpace (m + 1)) x = chartAt (EuclideanHalfSpace (m + 1)) y := by
  change closedCellChartAt x = closedCellChartAt y
  rw [closedCellChartAt, dif_pos hx, closedCellChartAt, dif_pos hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.closedCell_chart_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.closedCell_chart_eq target :: scope.openDecls } }

theorem chartBasisVecFiber_closedCell_of_norm_lt_one
    {α x : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1) (hx : ‖x.val‖ < 1)
    (i : Fin (Module.finrank ℝ EuN)) :
    chartBasisVecFiber (I := 𝓡∂ (m + 1)) α i x =
      chartModelBasis EuN i := by
  have ha : achart (EuclideanHalfSpace (m + 1)) α = achart (EuclideanHalfSpace (m + 1)) x :=
    Subtype.ext (closedCell_chart_eq hα hx)
  have hm : x ∈ (chartAt (EuclideanHalfSpace (m + 1)) α).source := by
    rw [closedCell_chart_eq hα hx]
    exact mem_chart_source _ x
  rw [chartBasisVecFiber,
    TangentBundle.symmL_trivializationAt_eq_core hm, ha]
  exact (tangentBundleCore (𝓡∂ (m + 1)) (ClosedCell (m + 1))).coordChange_self
    (achart (EuclideanHalfSpace (m + 1)) x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source _ x) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_closedCell_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_closedCell_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_closedCell_of_norm_lt_one ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_closedCell_of_norm_lt_one

end DifferentialGeometry.Tensor.Coordinates
