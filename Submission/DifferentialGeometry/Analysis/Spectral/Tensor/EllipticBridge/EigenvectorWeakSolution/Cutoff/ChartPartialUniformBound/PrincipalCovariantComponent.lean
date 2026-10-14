import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

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
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
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

def cutoffCovDerivComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent

noncomputable def cutoffCovNormSumFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) : M → ℝ :=
  fun b : M =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorRS_baseSet_eq_chart_source' (α : M) (r s : ℕ) :
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
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRS_baseSet_eq_chart_source'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRS_baseSet_eq_chart_source' target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma chartRSTwistInv_tensorCovDeriv_contMDiffOn'
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
  rw [show (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source from rfl] at htriv
  refine htriv.congr (fun b hb => ?_)
  rw [← triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (tangentSpaceModelContinuousLinearEquiv (I := I) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))]
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRS_baseSet_eq_chart_source' (I := I) (M := M) α r s]
    exact hb
  change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (tangentSpaceModelContinuousLinearEquiv (I := I) b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hb_base]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_tensorCovDeriv_contMDiffOn'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_tensorCovDeriv_contMDiffOn' target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma cutoffCovNormSqSum_continuousOn_chart_source
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
    (chartRSTwistInv_tensorCovDeriv_contMDiffOn' (I := I) (M := M)
      g r s S α i).continuousOn
  exact (hcov.norm).pow 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSqSum_continuousOn_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSqSum_continuousOn_chart_source target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffCovNormSumFun_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Continuous (cutoffCovNormSumFun (I := I) (M := M) g r s S α) := by
  classical
  set χ : C^∞⟮I, M; ℝ⟯ := chartKernelCutoff (I := I) (M := M) α with hχ_def
  set w : M → ℝ := fun b : M =>
    Real.sqrt
      (∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b
                (tangentSpaceModelContinuousLinearEquiv (I := I) b
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2) with hw_def
  have hfun_eq : cutoffCovNormSumFun (I := I) (M := M) g r s S α =
      fun b : M => ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b • w b := by
    funext b
    rw [cutoffCovNormSumFun]
    rfl
  rw [hfun_eq]
  refine continuous_of_tsupport (fun x hx => ?_)
  have hx_support : x ∈ tsupport ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    tsupport_smul_subset_left
      (f := fun b : M => ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) (g := w) hx
  have hx_source : x ∈ (chartAt H α).source :=
    chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx_support
  have hχ_contAt : ContinuousAt ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (χ.contMDiff.continuous).continuousAt
  have hw_contOn : ContinuousOn w ((chartAt H α).source) := by
    rw [hw_def]
    exact (cutoffCovNormSqSum_continuousOn_chart_source (I := I) (M := M)
      g r s S α).sqrt
  have hw_contAt : ContinuousAt w x :=
    hw_contOn.continuousAt ((chartAt H α).open_source.mem_nhds hx_source)
  exact hχ_contAt.smul hw_contAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun_continuous target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffCovNormSumFun_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Measurable (cutoffCovNormSumFun (I := I) (M := M) g r s S α) :=
  (cutoffCovNormSumFun_continuous (I := I) (M := M) g r s S α).measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun_measurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun_measurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun_measurable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovNormSumFun_measurable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartBasePoint_mem_goodSet'
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
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasePoint_mem_goodSet'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartBasePoint_mem_goodSet' target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffCovDerivComponent_le_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) :
    ‖cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx y‖ ≤
      (chartComponentProjectionUniformBound (E := E) r s •
        chartPushedRaw (I := I) (M := M) α
          (cutoffCovNormSumFun (I := I) (M := M) g r s S α)) y := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      chartBasePoint_mem_goodSet' (I := I) (M := M) α hy
    have hb_source : b ∈ (chartAt H α).source := by
      have := symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
      rwa [← hb_def] at this
    have hχ_nn : 0 ≤ ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartKernelCutoff_mem_Icc (I := I) (M := M) α b).1
    have hcut_eval : chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy]
    have hcov_eval : chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y =
          cutoffCovNormSumFun (I := I) (M := M) g r s S α b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) hy]
    have hcomp_eq :
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            (chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (tangentSpaceModelContinuousLinearEquiv (I := I) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b))))) := by
      rw [← tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
        g r s S α k hb_good]
      rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
        r s α hb_source
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (tangentSpaceModelContinuousLinearEquiv (I := I) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)))]
    set X : TensorRSModel r s ℝ E :=
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (tangentSpaceModelContinuousLinearEquiv (I := I) b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)))) with hX_def
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
          (fun i _ => sq_nonneg _) (Finset.mem_univ k)
      have hX_eq : ‖X‖ = Real.sqrt (‖X‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [hX_eq]
      exact Real.sqrt_le_sqrt hsq_le
    unfold cutoffCovDerivComponent
    rw [hcomp_eq, hcut_eval]
    have h_norm_prod :
        ‖((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            tensorChartComponentProjection (E := E) r s Idx Jdx X‖ =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ := by
      rw [norm_mul, Real.norm_of_nonneg hχ_nn]
    have hRHS_eq :
        (C_proj •
          chartPushedRaw (I := I) (M := M) α
            (cutoffCovNormSumFun (I := I) (M := M) g r s S α)) y =
          C_proj *
            (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
                : M → ℝ) b *
              Real.sqrt
                (∑ i : Fin (Module.finrank ℝ E),
                  ‖chartRSTwistInv (I := I) (M := M) α b r s
                      (TensorRSSpace.toModel
                        (tensorCovDerivAt (I := I) (M := M) g r s S b
                          (tangentSpaceModelContinuousLinearEquiv (I := I) b
                            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b))))‖ ^ 2)) := by
      change C_proj * chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y = _
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
    calc ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖
        ≤ ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (C_proj * w) :=
          mul_le_mul_of_nonneg_left h_proj_le_w hχ_nn
      _ = C_proj *
            (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
                : M → ℝ) b * w) := by
          ring
  · have hcov_zero : chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) hy
    have hcomp_zero : cutoffCovDerivComponent (I := I) (M := M)
        g r s S α k Idx Jdx y = 0 := by
      unfold cutoffCovDerivComponent
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
        _root_.MulZeroClass.zero_mul]
    rw [hcomp_zero, norm_zero]
    change (0 : ℝ) ≤ C_proj * chartPushedRaw (I := I) (M := M) α
      (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y
    rw [hcov_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent_le_chartPushedRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent_le_chartPushedRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent_le_chartPushedRaw ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffCovDerivComponent_le_chartPushedRaw

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
