import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartForm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartBasePoint_mem_goodSet
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      chartLeviCivitaGoodSet (I := I) α := by
  have hsrc : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) α,
    extChartAt_source]
  exact hsrc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasePoint_mem_goodSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasePoint_mem_goodSet target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorRS_baseSet_eq_chart_source (α : M) (r s : ℕ) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
  change ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet) =
        (chartAt H α).source
  change (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∩
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRS_baseSet_eq_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRS_baseSet_eq_chart_source target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tangent_baseSet_eq_chart_source (α : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tangent_baseSet_eq_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tangent_baseSet_eq_chart_source target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma chartRSTwistInv_tensorCovDeriv_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (tangentSpaceModelContinuousLinearEquiv (I := I) b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))))
      ((chartAt H α).source) := by
  classical
  have htriv := tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (I := I) (M := M) g r s S α i
  rw [tangent_baseSet_eq_chart_source (I := I) (M := M) α] at htriv
  refine htriv.congr (fun b hb => ?_)
  rw [← triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (tangentSpaceModelContinuousLinearEquiv (I := I) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))]
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRS_baseSet_eq_chart_source (I := I) (M := M) α r s]
    exact hb
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (tangentSpaceModelContinuousLinearEquiv (I := I) b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hb_base]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_tensorCovDeriv_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_tensorCovDeriv_contMDiffOn target :: scope.openDecls } }

private noncomputable def covNormSumFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) : M → ℝ :=
  fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covNormSqSum_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun b : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2)
      ((chartAt H α).source) := by
  refine continuousOn_finsetSum _ (fun i _ => ?_)
  have hcov : ContinuousOn
      (fun b : M =>
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (tangentSpaceModelContinuousLinearEquiv (I := I) b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))))
      ((chartAt H α).source) :=
    (chartRSTwistInv_tensorCovDeriv_contMDiffOn (I := I) (M := M)
      g r s S α i).continuousOn
  exact (hcov.norm).pow 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSqSum_continuousOn_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSqSum_continuousOn_chart_source target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSumFun_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Continuous (covNormSumFun (I := I) (M := M) g r s S α) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρ_def
  set w : M → ℝ := fun b : M =>
    Real.sqrt
      (∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b
                (tangentSpaceModelContinuousLinearEquiv (I := I) b
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2) with hw_def
  have hfun_eq : covNormSumFun (I := I) (M := M) g r s S α =
      fun b : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b • w b := by
    funext b
    rw [covNormSumFun]
    rfl
  rw [hfun_eq]
  refine continuous_of_tsupport (fun x hx => ?_)
  have hx_support : x ∈ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    tsupport_smul_subset_left
      (f := fun b : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) (g := w) hx
  have hx_source : x ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α hx_support
  have hρ_contAt : ContinuousAt ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (ρ.contMDiff.continuous).continuousAt
  have hw_contOn : ContinuousOn w ((chartAt H α).source) := by
    rw [hw_def]
    exact (covNormSqSum_continuousOn_chart_source (I := I) (M := M)
      g r s S α).sqrt
  have hw_contAt : ContinuousAt w x :=
    hw_contOn.continuousAt ((chartAt H α).open_source.mem_nhds hx_source)
  exact hρ_contAt.smul hw_contAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun_continuous target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSumFun_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Measurable (covNormSumFun (I := I) (M := M) g r s S α) :=
  (covNormSumFun_continuous (I := I) (M := M) g r s S α).measurable

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun_measurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun_measurable target :: scope.openDecls } }

omit [CompleteSpace E] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSumFun_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tsupport (covNormSumFun (I := I) (M := M) g r s S α) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  classical
  have hfun_eq : covNormSumFun (I := I) (M := M) g r s S α =
      fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b •
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (tangentSpaceModelContinuousLinearEquiv (I := I) b
                        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2) := by
    funext b
    rw [covNormSumFun]
    rfl
  rw [hfun_eq]
  exact tsupport_smul_subset_left
    (f := fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
    (g := fun b : M =>
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun_tsupport_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covNormSumFun_tsupport_subset target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_covDerivComponent_le_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) (y : EuclN) :
    ‖chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α)) y *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))‖ ≤
      (chartComponentProjectionUniformBound (E := E) r s •
        chartPushedRaw (I := I) (M := M) α
          (covNormSumFun (I := I) (M := M) g r s S α)) y := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      chartBasePoint_mem_goodSet (I := I) (M := M) α hy
    have hb_source : b ∈ (chartAt H α).source := by
      have := symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
      rwa [← hb_def] at this
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartAtlasPOU I M).nonneg α b
    have hρ_le_one : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b ≤ 1 :=
      (chartAtlasPOU I M).le_one α b
    have hpou_eval : chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) y =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) hy]
    have hcov_eval : chartPushedRaw (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) y =
          covNormSumFun (I := I) (M := M) g r s S α b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) hy]
    have hcomp_eq :
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            (chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))))) := by
      rw [← tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
        g r s S α m hb_good]
      rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
        r s α hb_source
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (tangentSpaceModelContinuousLinearEquiv (I := I) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)))]
    set X : TensorRSModel r s ℝ E :=
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (tangentSpaceModelContinuousLinearEquiv (I := I) b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)))) with hX_def
    have h_proj_le :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ ≤
          C_proj * ‖X‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_norm_le_sqrt :
        ‖X‖ ≤
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (tangentSpaceModelContinuousLinearEquiv (I := I) b
                        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2) := by
      have hsq_le :
          ‖X‖ ^ 2 ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (tangentSpaceModelContinuousLinearEquiv (I := I) b
                        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun i : Fin (Module.finrank ℝ E) =>
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (tangentSpaceModelContinuousLinearEquiv (I := I) b
                      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ m)
      have hX_eq : ‖X‖ = Real.sqrt (‖X‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [hX_eq]
      exact Real.sqrt_le_sqrt hsq_le
    rw [hcomp_eq, hpou_eval]
    have h_norm_prod :
        ‖((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            tensorChartComponentProjection (E := E) r s Idx Jdx X‖ =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ := by
      rw [norm_mul, Real.norm_of_nonneg hρ_nn]
    have hRHS_eq :
        (C_proj •
          chartPushedRaw (I := I) (M := M) α
            (covNormSumFun (I := I) (M := M) g r s S α)) y =
          C_proj *
            (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ i : Fin (Module.finrank ℝ E),
                  ‖chartRSTwistInv (I := I) (M := M) α b r s
                      (TensorRSSpace.toModel
                        (tensorCovDerivAt (I := I) (M := M) g r s S b
                          (tangentSpaceModelContinuousLinearEquiv (I := I) b
                            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2)) := by
      change C_proj * chartPushedRaw (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) y = _
      rw [hcov_eval]
      rfl
    rw [h_norm_prod, hRHS_eq]
    set w : ℝ :=
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2) with hw_def
    have hw_nn : 0 ≤ w := Real.sqrt_nonneg _
    have h_proj_le_w :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ ≤
          C_proj * w :=
      h_proj_le.trans
        (mul_le_mul_of_nonneg_left h_norm_le_sqrt hC_proj_nn)
    calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖
        ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (C_proj * w) :=
          mul_le_mul_of_nonneg_left h_proj_le_w hρ_nn
      _ = C_proj *
            (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b * w) := by
          ring
  · have hpou_zero : chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) hy
    have hcov_zero : chartPushedRaw (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) hy
    rw [hpou_zero, _root_.MulZeroClass.zero_mul, norm_zero]
    change (0 : ℝ) ≤ C_proj * chartPushedRaw (I := I) (M := M) α
      (covNormSumFun (I := I) (M := M) g r s S α) y
    rw [hcov_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_covDerivComponent_le_chartPushedRaw
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_covDerivComponent_le_chartPushedRaw target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_const_eLpNorm_pou_covDerivComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E))
      (m : Fin (Module.finrank ℝ E)),
      _root_.MeasureTheory.eLpNorm
        (fun y : EuclN =>
          chartPushedRaw (I := I) (M := M) α (⇑(chartAtlasPOU I M α)) y *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  S.toCcTensor.toSection
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))))
        2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  set Kα : Set M :=
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C_proj * (C_bridge * C_cov),
    mul_nonneg hC_proj_nn (mul_nonneg hC_bridge_pos.le hC_cov_nn), ?_⟩
  intro S Idx Jdx m
  set f : EuclN → ℝ := fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α (⇑(chartAtlasPOU I M α)) y *
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α
            S.toCcTensor.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
    with hf_def
  set v : M → ℝ := covNormSumFun (I := I) (M := M) g r s S.toCcTensor α
    with hv_def
  set μ : _root_.MeasureTheory.Measure EuclN :=
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have h_ptwise : ∀ y : EuclN,
      ‖f y‖ ≤ (C_proj • chartPushedRaw (I := I) (M := M) α v) y := by
    intro y
    rw [hf_def, hv_def, hC_proj_def]
    exact pou_covDerivComponent_le_chartPushedRaw (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx m y
  have h_mono :
      _root_.MeasureTheory.eLpNorm f 2 μ ≤
        eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    _root_.MeasureTheory.eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ =
        ‖C_proj‖ₑ * _root_.MeasureTheory.eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_const_smul C_proj (chartPushedRaw (I := I) (M := M) α v) 2 μ
  have hC_proj_enorm : ‖C_proj‖ₑ = ENNReal.ofReal C_proj := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_proj_nn]
  have hv_meas : Measurable v :=
    covNormSumFun_measurable (I := I) (M := M) g r s S.toCcTensor α
  have hv_support : tsupport v ⊆ Kα :=
    covNormSumFun_tsupport_subset (I := I) (M := M) g r s S.toCcTensor α
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ ≤
        ENNReal.ofReal C_bridge *
          _root_.MeasureTheory.eLpNorm v 2
            (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge hv_meas hv_support
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have hv_eq : v = fun b : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s
                    S.toCcTensor b
                    (tangentSpaceModelContinuousLinearEquiv (I := I) b
                      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2) := by
    rw [hv_def]
    funext b
    rw [covNormSumFun]
  have h_cov :
      eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := by
    rw [hv_eq]
    exact hC_cov S
  calc _root_.MeasureTheory.eLpNorm f 2 μ
      ≤ _root_.MeasureTheory.eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ := h_mono
    _ = ‖C_proj‖ₑ * _root_.MeasureTheory.eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
        h_smul
    _ = ENNReal.ofReal C_proj *
          eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ := by
        rw [hC_proj_enorm]
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
        exact mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞))) := by
        gcongr
    _ = ENNReal.ofReal (C_proj * (C_bridge * C_cov)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hC_proj_nn,
          ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_pou_covDerivComponent_le_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_pou_covDerivComponent_le_uniform target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ m : Fin (Module.finrank ℝ E),
        _root_.MeasureTheory.eLpNorm
          (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α (⇑(chartAtlasPOU I M α)) y *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    S.toCcTensor.toSection
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))))
          2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    exists_const_eLpNorm_pou_covDerivComponent_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨(Module.finrank ℝ E : ℝ) * C₀,
    mul_nonneg (Nat.cast_nonneg _) hC₀_nn, ?_⟩
  intro S Idx Jdx
  refine (Finset.sum_le_sum (fun m _ => hC₀ S Idx Jdx m)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * C₀) =
        (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal C₀ by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]]
  rw [mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
