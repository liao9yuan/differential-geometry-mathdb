import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Chart.Frobenius

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function _root_.FiberBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaFrobenius
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem smoothTensorPairing_eq_hessPairingChart_on_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) {x : M} (hx : x ∈ (chartAt H α).source) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  have hx_source_ext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hx_target_ext : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_source_ext
  have h_toE_mem : (toEuclidean (E := E)) (extChartAt I α x) ∈
      chartTargetEuclid (I := I) (M := M) α := by
    unfold chartTargetEuclid
    simp only [Set.mem_image]
    exact ⟨extChartAt I α x, hx_target_ext, rfl⟩
  have h_bridge := smoothTensorPairingChart_eq_hessPairingChart_pullback
    (I := I) (M := M) g α φ v h_toE_mem
  rw [h_bridge]
  have h_toE_inv : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) (extChartAt I α x)) = extChartAt I α x :=
    (toEuclidean (E := E)).symm_apply_apply _
  rw [h_toE_inv]
  rw [(extChartAt I α).left_inv hx_source_ext]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.smoothTensorPairing_eq_hessPairingChart_on_chartSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.smoothTensorPairing_eq_hessPairingChart_on_chartSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.smoothTensorPairing_eq_hessPairingChart_on_chartSource ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.smoothTensorPairing_eq_hessPairingChart_on_chartSource

theorem pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothTensorPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  have h_per_term : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      (chartAtlasPOU I M α : M → ℝ) x *
        smoothTensorPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    intro α hα
    by_cases h_pou : (chartAtlasPOU I M α : M → ℝ) x = 0
    · rw [h_pou, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
    · have h_x_support : x ∈ tsupport ((chartAtlasPOU I M α : M → ℝ)) := by
        apply subset_tsupport _
        simp only [Function.mem_support, ne_eq]
        exact h_pou
      have h_tsupport_subset :
          tsupport ((chartAtlasPOU I M α : M → ℝ)) ⊆ (chartAt H α).source :=
        chartAtlasPOU_isSubordinate I M α
      have h_x_chart : x ∈ (chartAt H α).source := h_tsupport_subset h_x_support
      congr 1
      exact smoothTensorPairing_eq_hessPairingChart_on_chartSource
        (I := I) (M := M) g α φ v h_x_chart
  rw [Finset.sum_congr rfl h_per_term]
  rw [← Finset.sum_mul]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x]
  rw [one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp.pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise

end HessianChartAlphaLp
end Laplacian
end Analysis
end DifferentialGeometry

end
