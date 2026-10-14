import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.PullbackGram
import Submission.DifferentialGeometry.Topology.Handle.ClosedCell.InteriorCoordinates
import Submission.DifferentialGeometry.Geometry.Metric.Family.ClosedCellPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

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

theorem gramOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) {y : W}
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let A : W → M := fun z => closedCellChartMap Φ c r
    ((extChartAt (𝓡∂ (m + 1)) α).symm ((toEuclidean (E := V)).symm z))
  let B : W → M := fun z =>
    Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))
  have heq : A =ᶠ[𝓝 y] B := by
    have hO : IsOpen (toEuclidean (E := V) ''
        interior (extChartAt (𝓡∂ (m + 1)) α).target) :=
      (toEuclidean (E := V)).toHomeomorph.isOpenMap _ isOpen_interior
    filter_upwards [hO.mem_nhds hy] with z hz
    have htarget : (toEuclidean (E := V)).symm z ∈
        (extChartAt (𝓡∂ (m + 1)) α).target :=
      toEuclidean_symm_mem_target ((_root_.Set.image_mono interior_subset) hz)
    dsimp only [A, B, closedCellChartMap]
    rw [closedCell_extChartAt_symm_val_of_norm_lt_one α hα _ htarget]
  have hvalue := heq.eq_of_nhds
  have hderiv := heq.mfderiv_eq (I := 𝓘(ℝ, W)) (I' := I)
  have hgram := gramOnEuclid_pullback (g t) (closedCellChartMap Φ c r)
    (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (injective_mfderiv_closedCellChartMap Φ c hr hsource) α hy i j
  change gramOnEuclid ((g t).pullback (closedCellChartMap Φ c r)
    (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (injective_mfderiv_closedCellChartMap Φ c hr hsource)) α i j y = _
  rw [hgram]
  change pullbackMetricCoefficients (g t) A y _ _ = pullbackMetricCoefficients (g t) B y _ _
  simp only [pullbackMetricCoefficients_apply]
  rw [hderiv, hvalue]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_closedCellPullbackMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_closedCellPullbackMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_closedCellPullbackMetricFamily ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_closedCellPullbackMetricFamily

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
