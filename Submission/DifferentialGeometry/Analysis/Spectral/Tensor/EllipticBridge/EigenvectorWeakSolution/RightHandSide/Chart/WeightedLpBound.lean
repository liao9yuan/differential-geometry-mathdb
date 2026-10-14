import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RotationL2Bounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.WeightedL2Bounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergenceL2Bound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

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

section Aggregation

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma eLpNorm_sum_le_const_mul_aggregate
    {ι : Type*} [Fintype ι] {μ : _root_.MeasureTheory.Measure EuclN} (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, _root_.MeasureTheory.MemLp (F j) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ _root_.MeasureTheory.eLpNorm (F j) 2 μ ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ j : ι, F j y) 2 μ ≤ ENNReal.ofReal C * A := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j y) = ∑ j : ι, F j := by
    funext y
    exact (Finset.sum_apply y Finset.univ F).symm
  rw [h_fun]
  have h_tri : _root_.MeasureTheory.eLpNorm (∑ j : ι, F j) 2 μ ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j) 2 μ :=
    _root_.MeasureTheory.eLpNorm_sum_le (fun j _ => (hF j).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    _root_.MeasureTheory.eLpNorm (∑ j : ι, F j) 2 μ
        ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate target :: scope.openDecls } }

end Aggregation

section Aggregate

private lemma le_sixSum (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a₁ ≤ a₁ + a₂ := le_self_add
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₂ ≤ a₁ + a₂ := le_add_self
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₃ ≤ a₁ + a₂ + a₃ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₄ ≤ a₁ + a₂ + a₃ + a₄ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · exact le_add_self

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sixSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sixSum target :: scope.openDecls } }

end Aggregate

section MainBound

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenIdx_val_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenIdx_val_pos target :: scope.openDecls } }

end MainBound

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_sum_le_const_mul_aggregate_uniform
    {ι : Type*} [Fintype ι] {ν : Type*} {μ : _root_.MeasureTheory.Measure EuclN}
    (F : ι → ν → EuclN → ℝ) (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), _root_.MeasureTheory.MemLp (F j n) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, _root_.MeasureTheory.eLpNorm (F j n) 2 μ ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν,
        eLpNorm (fun y => ∑ j : ι, F j n y) 2 μ ≤ ENNReal.ofReal C * A n := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j n y) = ∑ j : ι, F j n := by
    funext y
    exact (Finset.sum_apply y Finset.univ (fun j => F j n)).symm
  rw [h_fun]
  have h_tri : _root_.MeasureTheory.eLpNorm (∑ j : ι, F j n) 2 μ ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j n) 2 μ :=
    _root_.MeasureTheory.eLpNorm_sum_le (fun j _ => (hF j n).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j n) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    _root_.MeasureTheory.eLpNorm (∑ j : ι, F j n) 2 μ
        ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j n) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate_uniform target :: scope.openDecls } }

section TermMemLp

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_memLp_unconditional :
    MemLp (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold eigenvectorChartComponentFun
  exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossLeftContraction_summand_memLp_unconditional
    (P Q : TensorCompIdx (E := E) r (s + 1)) :
    _root_.MeasureTheory.MemLp
      (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_aezero :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    rw [crossLeftLimitComponent]
    exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
      (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
      (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
      g r s i α P)
    h_aezero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction_summand_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction_summand_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossLeftContraction_memLp_unconditional :
    MemLp (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold eigenvectorChartCrossLeftContraction
  exact _root_.MeasureTheory.memLp_finsetSum _
    (fun P _ => _root_.MeasureTheory.memLp_finsetSum _
      (fun Q _ => eigenvectorChartCrossLeftContraction_summand_memLp_unconditional (I := I) (M := M)
        g r s i α P₀ P Q))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossRightContraction_summand_memLp_unconditional
    (P Q : TensorCompIdx (E := E) r s) :
    _root_.MeasureTheory.MemLp
      (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_aezero :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    rw [crossRightLimitComponent]
    exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
      (I := I) (M := M) g r s
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
      g r s i α P)
    h_aezero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction_summand_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction_summand_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossRightContraction_memLp_unconditional :
    MemLp (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold eigenvectorChartCrossRightContraction
  exact _root_.MeasureTheory.memLp_finsetSum _
    (fun P _ => _root_.MeasureTheory.memLp_finsetSum _
      (fun Q _ => eigenvectorChartCrossRightContraction_summand_memLp_unconditional (I := I) (M := M)
        g r s i α P₀ P Q))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma covPrincipalRotationCoeffLimit_memLp_unconditional :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  covPrincipalRotationCoeffLimit_memLp_weighted
    (I := I) (M := M) g r s i α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma covLowerOrderRotationValueCoeffLimit_memLp_unconditional :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  covLowerOrderRotationValueCoeffLimit_memLp_weighted
    (I := I) (M := M) g r s i α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_memLp_unconditional :
    _root_.MeasureTheory.MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  exact _root_.MeasureTheory.memLp_finsetSum _
    (fun l _ => weightedGradCoeffDivLimit_memLp_weighted
      (I := I) (M := M) g r s i α P₀ l)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_sum_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_sum_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
  Filter.Eventually.of_forall (fun _y hy =>
    Finset.sum_eq_zero (fun l _ =>
      weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ l hy))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma crossRightGradCoeffDivLimit_memLp_weighted :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memLp_weighted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memLp_weighted target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartWeightedDivergence_memLp_unconditional :
    MemLp (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold eigenvectorChartWeightedDivergence
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (weightedGradCoeffDivLimit_sum_memLp_unconditional (I := I) (M := M)
      g r s i α P₀)
    (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence_memLp_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossRightDivergence_memLp_unconditional :
    MemLp (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold eigenvectorChartCrossRightDivergence
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
      g r s i α P₀)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence_memLp_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence_memLp_unconditional target :: scope.openDecls } }

end TermMemLp

section Aggregate

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private def eigenvectorChartComponentELpNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
      g r s i α P₀) 2
    ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentELpNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentELpNorm target :: scope.openDecls } }

private def crossLeftLimitELpNormSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r (s + 1),
    eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitELpNormSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitELpNormSum target :: scope.openDecls } }

private def crossRightLimitELpNormSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    eLpNorm ((crossRightLimitComponent (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitELpNormSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitELpNormSum target :: scope.openDecls } }

private def partialLimitELpNormSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      eLpNorm ((partialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLimitELpNormSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLimitELpNormSum target :: scope.openDecls } }

private def componentLimitELpNormSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    eLpNorm ((componentLpLimit (I := I) (M := M) g r s i α p :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLimitELpNormSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLimitELpNormSum target :: scope.openDecls } }

private def cutoffPartialLimitELpNormSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
          g r s i α P l :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLimitELpNormSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLimitELpNormSum target :: scope.openDecls } }

private def eigenvectorChartRHSELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  eigenvectorChartComponentELpNorm (I := I) (M := M) g r s i α P₀ +
    crossLeftLimitELpNormSum (I := I) (M := M) g r s i α P₀ +
    crossRightLimitELpNormSum (I := I) (M := M) g r s i α P₀ +
    partialLimitELpNormSum (I := I) (M := M) g r s i α P₀ +
    componentLimitELpNormSum (I := I) (M := M) g r s i α P₀ +
    cutoffPartialLimitELpNormSum (I := I) (M := M) g r s i α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSELpControl target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentELpNorm_le_rhsELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentELpNorm (I := I) (M := M) g r s i α P₀
      ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  rw [eigenvectorChartRHSELpControl]
  exact (le_sixSum _ _ _ _ _ _).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentELpNorm_le_rhsELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentELpNorm_le_rhsELpControl target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma crossLeftLimitELpNormSum_le_rhsELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    crossLeftLimitELpNormSum (I := I) (M := M) g r s i α P₀
      ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  rw [eigenvectorChartRHSELpControl]
  exact (le_sixSum _ _ _ _ _ _).2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitELpNormSum_le_rhsELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitELpNormSum_le_rhsELpControl target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma crossRightLimitELpNormSum_le_rhsELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    crossRightLimitELpNormSum (I := I) (M := M) g r s i α P₀
      ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  rw [eigenvectorChartRHSELpControl]
  exact (le_sixSum _ _ _ _ _ _).2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitELpNormSum_le_rhsELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitELpNormSum_le_rhsELpControl target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma partialLimitELpNormSum_le_rhsELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    partialLimitELpNormSum (I := I) (M := M) g r s i α P₀
      ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  rw [eigenvectorChartRHSELpControl]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLimitELpNormSum_le_rhsELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLimitELpNormSum_le_rhsELpControl target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma componentLimitELpNormSum_le_rhsELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    componentLimitELpNormSum (I := I) (M := M) g r s i α P₀
      ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  rw [eigenvectorChartRHSELpControl]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLimitELpNormSum_le_rhsELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLimitELpNormSum_le_rhsELpControl target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma cutoffPartialLimitELpNormSum_le_rhsELpControl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    cutoffPartialLimitELpNormSum (I := I) (M := M) g r s i α P₀
      ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  rw [eigenvectorChartRHSELpControl]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.2.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLimitELpNormSum_le_rhsELpControl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLimitELpNormSum_le_rhsELpControl target :: scope.openDecls } }

end Aggregate

section TermBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  refine ⟨1, by norm_num, fun i => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  change eigenvectorChartComponentELpNorm (I := I) (M := M) g r s i α P₀ ≤
    eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
  exact eigenvectorChartComponentELpNorm_le_rhsELpControl (I := I) (M := M)
    g r s i α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossLeftContraction_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set F : (TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1)) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have hF_memLp : ∀ (x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1))
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F x i) 2 μw := by
    intro x i
    rw [hμw_def, hF_def]
    exact eigenvectorChartCrossLeftContraction_summand_memLp_unconditional (I := I) (M := M)
      g r s i α P₀ x.1 x.2
  have hF_bd : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        _root_.MeasureTheory.eLpNorm (F x i) 2 μw
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    intro x
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    refine ⟨C, hC_nn, fun i => ?_⟩
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    have h_atom_le :
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α x.1 :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
      refine le_trans ?_
        (crossLeftLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
          g r s i α P₀)
      rw [hμw_def, crossLeftLimitELpNormSum]
      exact Finset.single_le_sum
        (f := fun P => _root_.MeasureTheory.eLpNorm ((crossLeftLimitComponent
            (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd _
      (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
        g r s i α x.1) h_aezero) ?_
    gcongr
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), F x i y)
      = eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ := by
    funext y
    simp only [eigenvectorChartCrossLeftContraction, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossRightContraction_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set F : (TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossRightLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have hF_memLp : ∀ (x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s)
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F x i) 2 μw := by
    intro x i
    rw [hμw_def, hF_def]
    exact eigenvectorChartCrossRightContraction_summand_memLp_unconditional (I := I) (M := M)
      g r s i α P₀ x.1 x.2
  have hF_bd : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        _root_.MeasureTheory.eLpNorm (F x i) 2 μw
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    intro x
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    refine ⟨C, hC_nn, fun i => ?_⟩
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    have h_atom_le :
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s i α x.1 :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
      refine le_trans ?_
        (crossRightLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
          g r s i α P₀)
      rw [hμw_def, crossRightLimitELpNormSum]
      exact Finset.single_le_sum
        (f := fun P => _root_.MeasureTheory.eLpNorm ((crossRightLimitComponent
            (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd _
      (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
        g r s i α x.1) h_aezero) ?_
    gcongr
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, F x i y)
      = eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ := by
    funext y
    simp only [eigenvectorChartCrossRightContraction, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma covPrincipalRotationCoeffLimit_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eLpNorm_covPrincipalRotationCoeffLimit_le_uniform
      (I := I) (M := M) g r s α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine le_trans (hC_bd i) ?_
  gcongr
  exact partialLimitELpNormSum_le_rhsELpControl (I := I) (M := M) g r s i α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma covLowerOrderRotationValueCoeffLimit_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform
      (I := I) (M := M) g r s α P₀
  refine ⟨2 * C, by positivity, fun i => ?_⟩
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (partialLimitELpNormSum_le_rhsELpControl (I := I) (M := M) g r s i α P₀)
      (componentLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
        g r s i α P₀)
  refine le_trans (hC_bd i) ?_
  calc
    ENNReal.ofReal C *
        ((∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))))
        ≤ ENNReal.ofReal C *
            (2 * eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
        rw [← ENNReal.ofReal_ofNat 2, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
          mul_comm C 2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        _root_.MeasureTheory.eLpNorm
            (fun y => ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set F : Fin (Module.finrank ℝ E) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun l i => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l with hF_def
  have hF_memLp : ∀ (l : Fin (Module.finrank ℝ E))
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F l i) 2 μw := by
    intro l i
    rw [hμw_def, hF_def]
    exact weightedGradCoeffDivLimit_memLp_weighted
      (I := I) (M := M) g r s i α P₀ l
  have hF_bd : ∀ l : Fin (Module.finrank ℝ E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        _root_.MeasureTheory.eLpNorm (F l i) 2 μw
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    intro l
    obtain ⟨C, hC_nn, hC_bd⟩ :=
      eLpNorm_weightedGradCoeffDivLimit_le_uniform
        (I := I) (M := M) g r s α P₀ l
    refine ⟨2 * C, by positivity, fun i => ?_⟩
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd i) ?_
    have h_sum_le :
        (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              ∑ l' : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s i α p l' :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
        ≤ 2 * eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
      rw [two_mul]
      exact add_le_add
        (componentLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
          g r s i α P₀)
        (partialLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
          g r s i α P₀)
    calc
      ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s i α p l' :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                    EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α))))
          ≤ ENNReal.ofReal C *
              (2 * eigenvectorChartRHSELpControl (I := I) (M := M)
                g r s i α P₀) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
          rw [← ENNReal.ofReal_ofNat 2, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [hμw_def] at hC_bd
  exact hC_bd i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartWeightedDivergence_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀
  refine ⟨C₁ * C₂, by positivity, fun i => ?_⟩
  unfold eigenvectorChartWeightedDivergence
  calc
    _root_.MeasureTheory.eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            _root_.MeasureTheory.eLpNorm
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
          hC₁_bd _
            (weightedGradCoeffDivLimit_sum_memLp_unconditional (I := I) (M := M)
              g r s i α P₀)
            (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel_unconditional
              (I := I) (M := M) g r s i α P₀)
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀) := by
        gcongr
        exact hC₂_bd i
    _ = ENNReal.ofReal (C₁ * C₂) *
          eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartCrossRightDivergence_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    eLpNorm_crossRightGradCoeffDivLimit_le_uniform
      (I := I) (M := M) g r s α P₀
  refine ⟨C₁ * (2 * C₂), by positivity, fun i => ?_⟩
  unfold eigenvectorChartCrossRightDivergence
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          eLpNorm ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ l : Fin (Module.finrank ℝ E),
              eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (crossRightLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
        g r s i α P₀)
      (cutoffPartialLimitELpNormSum_le_rhsELpControl (I := I) (M := M)
        g r s i α P₀)
  calc
    _root_.MeasureTheory.eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
          hC₁_bd _
            (crossRightGradCoeffDivLimit_memLp_weighted
              (I := I) (M := M) g r s i α P₀)
            (Filter.Eventually.of_forall (fun y hy =>
              crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s i α P₀ hy))
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * eigenvectorChartRHSELpControl (I := I) (M := M)
              g r s i α P₀)) := by
        gcongr
        exact le_trans (hC₂_bd i) (by gcongr)
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat 2]
        ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

end TermBounds

section BracketBound

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSNumerator_eLpNorm_le_uniform_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
  classical
  obtain ⟨D1, hD1_nn, hD1⟩ := eigenvectorChartComponentFun_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D2, hD2_nn, hD2⟩ := eigenvectorChartCrossLeftContraction_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D3, hD3_nn, hD3⟩ := eigenvectorChartCrossRightContraction_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D4, hD4_nn, hD4⟩ := covPrincipalRotationCoeffLimit_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D5, hD5_nn, hD5⟩ := covLowerOrderRotationValueCoeffLimit_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D6, hD6_nn, hD6⟩ := eigenvectorChartWeightedDivergence_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  obtain ⟨D7, hD7_nn, hD7⟩ := eigenvectorChartCrossRightDivergence_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, fun i => ?_⟩
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hM1 := eigenvectorChartComponentFun_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM2 := eigenvectorChartCrossLeftContraction_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM3 := eigenvectorChartCrossRightContraction_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM4 := covPrincipalRotationCoeffLimit_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM5 := covLowerOrderRotationValueCoeffLimit_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM6 := eigenvectorChartWeightedDivergence_memLp_unconditional (I := I) (M := M) g r s i α P₀
  have hM7 := eigenvectorChartCrossRightDivergence_memLp_unconditional (I := I) (M := M) g r s i α P₀
  rw [← hμw_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  have hB12 := hM1.sub hM2
  have hB123 := hB12.add hM3
  have hB1234 := hB123.sub hM4
  have hB12345 := hB1234.sub hM5
  have hB123456 := hB12345.add hM6
  have h_tri :
      eLpNorm (eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀) 2 μw
        ≤ _root_.MeasureTheory.eLpNorm (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀) 2 μw
          + _root_.MeasureTheory.eLpNorm (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀) 2 μw
          + _root_.MeasureTheory.eLpNorm (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀) 2 μw
          + _root_.MeasureTheory.eLpNorm (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀) 2 μw
          + _root_.MeasureTheory.eLpNorm (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀) 2 μw
          + _root_.MeasureTheory.eLpNorm (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀) 2 μw
          + _root_.MeasureTheory.eLpNorm (eigenvectorChartCrossRightDivergence (I := I) (M := M)
              g r s i α P₀) 2 μw := by
    rw [eigenvectorChartRHSNumerator]
    refine le_trans (_root_.MeasureTheory.eLpNorm_sub_le hB123456.aestronglyMeasurable
      hM7.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (_root_.MeasureTheory.eLpNorm_add_le hB12345.aestronglyMeasurable
      hM6.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (_root_.MeasureTheory.eLpNorm_sub_le hB1234.aestronglyMeasurable
      hM5.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (_root_.MeasureTheory.eLpNorm_sub_le hB123.aestronglyMeasurable
      hM4.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (_root_.MeasureTheory.eLpNorm_add_le hB12.aestronglyMeasurable
      hM3.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact _root_.MeasureTheory.eLpNorm_sub_le hM1.aestronglyMeasurable
      hM2.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  have h_seven :
      eLpNorm (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀) 2 μw
        + _root_.MeasureTheory.eLpNorm (eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀) 2 μw
        + _root_.MeasureTheory.eLpNorm (eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀) 2 μw
        + _root_.MeasureTheory.eLpNorm (covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀) 2 μw
        + _root_.MeasureTheory.eLpNorm (covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀) 2 μw
        + _root_.MeasureTheory.eLpNorm (eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀) 2 μw
        + _root_.MeasureTheory.eLpNorm (eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀) 2 μw
      ≤ ENNReal.ofReal D1 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D2 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D3 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D4 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D5 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D6 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀
          + ENNReal.ofReal D7 *
            eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (hD1 i) (hD2 i)) (hD3 i)) (hD4 i)) (hD5 i)) (hD6 i)) (hD7 i)
  refine le_trans h_seven ?_
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSNumerator_eLpNorm_le_uniform_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSNumerator_eLpNorm_le_uniform_unconditional target :: scope.openDecls } }

end BracketBound

section MainBound

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
theorem eigenvectorChartRHS_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            (_root_.MeasureTheory.eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
                  g r s i α P₀) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r (s + 1),
                  eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                      g r s i α P :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                      g r s i α P :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ k : Fin (Module.finrank ℝ E),
                    eLpNorm ((partialLpLimit (I := I) (M := M)
                        g r s i α P k :
                      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  eLpNorm ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s i α P l :
                      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSNumerator_eLpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hC_bd_i := hC_bd i
  have h_smul_eq :
      eLpNorm (eigenvectorChartRHS (I := I) (M := M)
          g r s i α P₀) 2 μw
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (eigenvectorChartRHSNumerator (I := I) (M := M)
            g r s i α P₀) 2 μw := by
    rw [eigenvectorChartRHS_eq_eigenvalue_inv_smul_numerator (I := I) (M := M)
      g r s i α P₀]
    have h := _root_.MeasureTheory.eLpNorm_const_smul (μ := μw) (p := 2) (i.fst.val)⁻¹
      (eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀)
    rw [Real.enorm_of_nonneg hμ_inv_nn] at h
    exact h
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (eigenvectorChartRHSNumerator (I := I) (M := M)
            g r s i α P₀) 2 μw
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          eigenvectorChartRHSELpControl (I := I) (M := M) g r s i α P₀ := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  exact h_step

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eLpNorm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eLpNorm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eLpNorm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eLpNorm_le_uniform

end MainBound
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
