import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Components
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotChartSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovariantDerivativeBounds.SlotCorrection.Kernel
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.FiberFromModel
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.FiberToModel
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.MeasureTheory.Integral.IntegrableOn

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
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem


section CovariantAtomsChartSource

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_measurableSet (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_measurableSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_measurableSet target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private lemma chartTensorRSCovariantDerivative_eq_of_eq_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X Y : Π b' : M, TangentSpace I b') {b : M} (hb : X b = Y b) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T Y b := by
  classical
  rw [chartTensorRSCovariantDerivative_def, chartTensorRSCovariantDerivative_def]
  rw [show tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (Y b) from by rw [hb]]
  have hParabolic :
      chartLeviCivitaParallelCLM (I := I) g α b X =
        chartLeviCivitaParallelCLM (I := I) g α b Y := by
    unfold chartLeviCivitaParallelCLM
    rw [hb]
  have hInput : ∀ k : Fin r,
      chartTensorRSInputSlotCorrection (I := I) r s g α T X b k =
        chartTensorRSInputSlotCorrection (I := I) r s g α T Y b k := by
    intro k
    unfold chartTensorRSInputSlotCorrection
    rw [hParabolic]
  have hOutput : ∀ l : Fin s,
      chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l =
        chartTensorRSOutputSlotCorrection (I := I) r s g α T Y b l := by
    intro l
    unfold chartTensorRSOutputSlotCorrection
    rw [hParabolic]
  rw [Finset.sum_congr rfl (fun k _ => hInput k)]
  rw [Finset.sum_congr rfl (fun l _ => hOutput l)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSCovariantDerivative_eq_of_eq_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSCovariantDerivative_eq_of_eq_at target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ (chartAt H α).source) :
    chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') X b =
      tensorCovDerivAt (I := I) (M := M) g r s S b (X b) := by
  classical
  obtain ⟨Y, hYb⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (n := (⊤ : ℕ∞))
      (V := (TangentSpace I : M → Type _)) b (X b)
  have hswap :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') X b =
        chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b :=
    chartTensorRSCovariantDerivative_eq_of_eq_at
      (I := I) g r s α (fun b' => S.toSection b') X Y.toFun hYb.symm
  rw [hswap]
  have hb_goodSet : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
        extChartAt_source_eq_chartAt_source (I := I)]
    exact hb
  have hagree :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet
      (I := I) (M := M) g r s α S.toSection Y hb_goodSet
  change chartTensorRSCovariantDerivative (I := I) r s g α
      (fun b' => S.toSection b') Y.toFun b =
    TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X b)
  have hagree' :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b =
        TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) (fun b' => S.toSection b') b (Y.toFun b) :=
    hagree
  rw [hagree']
  have hYb' : Y.toFun b = X b := hYb
  rw [hYb']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b) =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
        ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)⟩).2 := by
  classical
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  have hbaseRS : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    all_goals
      change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoe := (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseRS
  change ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b)
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)) = _
  exact congrFun hcoe _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b))
      ((chartAt H α).source) := by
  classical
  have hbase :
      ContinuousOn
        (fun b : M =>
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)⟩).2)
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    (tensorCovDeriv_chartBasis_trivImage_contMDiffOn
      (I := I) (M := M) g r s S α k).continuousOn
  have hbase_eq :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  rw [hbase_eq] at hbase
  refine hbase.congr ?_
  intro b hb_chart
  exact triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (I := I) (M := M) g r s α S hb_chart k

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_chartTensorRSCovariantDerivative_continuousOn_chart_source target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ∑ k : Fin (Module.finrank ℝ E),
          ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖
            ^ 2)
      ((chartAt H α).source) := by
  classical
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  have h_proj := triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (I := I) (M := M) g r s α S k
  have h_norm : ContinuousOn
      (fun b : M =>
        ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖)
      ((chartAt H α).source) := h_proj.norm
  exact h_norm.pow 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_mul_sqrt_sum_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((chartAt H α).source) := by
  classical
  have h_pou_cont : Continuous
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) :=
    ((chartAtlasPOU I M α).contMDiff.continuous)
  have h_pou_on : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) := h_pou_cont.continuousOn
  have h_sumsq :=
    norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
      (I := I) (M := M) g r s α S
  have h_sqrt : ContinuousOn
      (fun b : M =>
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((chartAt H α).source) :=
    Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou_on.mul h_sqrt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_continuousOn_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_continuousOn_chart_source target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_mul_sqrt_sum_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  refine (pou_mul_sqrt_sum_continuousOn_chart_source
    (I := I) (M := M) g r s α S).mono ?_
  intro b hb
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_continuousOn_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_continuousOn_pouTsupport target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pou_mul_sqrt_sum_zero_outside_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∉ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2) = 0 := by
  classical
  have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
    by_contra hne
    exact hb (subset_tsupport _ hne)
  rw [hρ_zero, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_zero_outside_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_zero_outside_pouTsupport target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pou_mul_sqrt_sum_eq_indicator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) =
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := by
  classical
  funext b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · rw [Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem hb]
    exact pou_mul_sqrt_sum_zero_outside_pouTsupport
      (I := I) (M := M) g r s α S hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_eq_indicator
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_eq_indicator target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (pou_mul_sqrt_sum_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet (I := I) (M := M) α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  rw [pou_mul_sqrt_sum_eq_indicator (I := I) (M := M) g r s α S.toCcTensor]
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet (I := I) (M := M) α)]
  exact pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M} (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b) =
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b))) := by
  classical
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (I := I) (M := M) r s α (b := b) hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv target :: scope.openDecls } }

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)))‖ ^ 2) := by
  classical
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hb_chart : b ∈ (chartAt H α).source := hb_base
    have hsumeq :
        (∑ k : Fin (Module.finrank ℝ E),
          ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b')
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
          ∑ k : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)))‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
        (I := I) (M := M) g r s α S hb_chart k]
    rw [hsumeq]
  · have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hρ_zero]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        _root_.MeasureTheory.eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ k : Fin (Module.finrank ℝ E),
                    ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                          ℝ b
                      (chartTensorRSCovariantDerivative (I := I) r s g α
                        (fun b' => S.toCcTensor.toSection b')
                        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_eL⟩ :=
    exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_pt :
      (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) =
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartRSTwistInv (I := I) (M := M) α b r s
                    (TensorRSSpace.toModel
                      (tensorCovDerivAt (I := I) (M := M) g r s
                        S.toCcTensor b
                        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)))‖ ^ 2)) := by
    funext b
    exact pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
      (I := I) (M := M) g r s α S.toCcTensor b
  rw [h_pt]
  exact h_eL S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq

end CovariantAtomsChartSource

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
