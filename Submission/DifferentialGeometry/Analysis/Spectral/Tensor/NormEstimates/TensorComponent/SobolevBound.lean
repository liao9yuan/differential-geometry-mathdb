import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentWkpNormBoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponent.GradientLpNormPerIndex
import Mathlib.Topology.Compactness.LocallyFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

section ScalarUniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

noncomputable def chartAtlasPOUActiveFinset
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] : Finset M :=
  ((chartAtlasPOU I M).locallyFinite.finite_nonempty_of_compact).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOUActiveFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOUActiveFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOUActiveFinset ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOUActiveFinset

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma mem_chartAtlasPOU_activeFinset_iff (α : M) :
    α ∈ chartAtlasPOUActiveFinset I M ↔
      (Function.support (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).Nonempty := by
  classical
  unfold chartAtlasPOUActiveFinset
  exact Set.Finite.mem_toFinset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_chartAtlasPOU_activeFinset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_chartAtlasPOU_activeFinset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_chartAtlasPOU_activeFinset_iff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_chartAtlasPOU_activeFinset_iff

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartAtlasPOU_eq_zero_of_notMem_activeFinset
    {α : M} (hα : α ∉ chartAtlasPOUActiveFinset I M) :
    ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
  classical
  intro x
  have h_empty :
      ¬ (Function.support (fun y : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y)).Nonempty := by
    intro h
    exact hα ((mem_chartAtlasPOU_activeFinset_iff (I := I) (M := M) α).mpr h)
  rw [Set.not_nonempty_iff_eq_empty, Function.support_eq_empty_iff] at h_empty
  have := congrFun h_empty x
  simpa using this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOU_eq_zero_of_notMem_activeFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOU_eq_zero_of_notMem_activeFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOU_eq_zero_of_notMem_activeFinset ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOU_eq_zero_of_notMem_activeFinset

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComponentScalar_eq_zero_of_pou_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (h_zero : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx = 0 := by
  classical
  funext x
  change (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x =
    (0 : M → ℝ) x
  rw [h_zero x, _root_.MulZeroClass.zero_mul]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eq_zero_of_pou_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eq_zero_of_pou_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eq_zero_of_pou_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eq_zero_of_pou_zero

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOUActiveFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact _root_.MeasureTheory.eLpNorm_zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive target :: scope.openDecls } }

private noncomputable def perAlphaConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma perAlphaConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant_nonneg target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma perAlphaConstant_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
  (Classical.choose_spec (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)).2 S Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant_bound target :: scope.openDecls } }

private noncomputable def totalActiveConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOUActiveFinset I M,
    perAlphaConstant (I := I) (M := M) g r s α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.totalActiveConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.totalActiveConstant target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma totalActiveConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaConstant_nonneg (I := I) (M := M) g r s α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.totalActiveConstant_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.totalActiveConstant_nonneg target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma perAlphaConstant_le_totalActiveConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOUActiveFinset I M) :
    perAlphaConstant (I := I) (M := M) g r s α ≤
      totalActiveConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveConstant
  have h_split :
      ∑ β ∈ chartAtlasPOUActiveFinset I M,
        perAlphaConstant (I := I) (M := M) g r s β =
        perAlphaConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOUActiveFinset I M).erase α,
          perAlphaConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOUActiveFinset I M).erase α,
            perAlphaConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaConstant_nonneg (I := I) (M := M) g r s β)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant_le_totalActiveConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perAlphaConstant_le_totalActiveConstant target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensor g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  refine ⟨totalActiveConstant (I := I) (M := M) g r s,
    totalActiveConstant_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOUActiveFinset I M
  · have h_per :
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
      perAlphaConstant_bound (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal (totalActiveConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaConstant_le_totalActiveConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) ≤
          ENNReal.ofReal (totalActiveConstant (I := I) (M := M) g r s) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le)
    exact h_per.trans h_envelope_le
  · rw [eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
      (I := I) (M := M) g r s hα S Idx Jdx]
    exact zero_le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_smoothCcTensor target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Norm_eq_norm_toCcTensor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Norm_eq_norm_toCcTensor target :: scope.openDecls } }

private lemma coe_nnnorm_eq_ofReal_norm_scalar {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm_scalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm_scalar target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm_scalar S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_tensorL2Norm_le_norm_ennreal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_tensorL2Norm_le_norm_ennreal target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₀, hC₀_nn, h_smoothCc⟩ :=
    tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
      (I := I) (M := M) g r s
  refine ⟨C₀, hC₀_nn, ?_⟩
  intro S α Idx Jdx
  have h_smoothCc' :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₀ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor α Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C₀ *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le)
  exact h_smoothCc'.trans h_rhs_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_eLpNorm_le_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) :=
  tensorChartComponentScalar_eLpNorm_le
    (I := I) (M := M) g r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_forall ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_forall

end ScalarUniform

section GradUniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_2 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_3 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_3 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_3 target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (h_u_zero : u = 0) :
    (fun b : M => Real.sqrt
        (g.inner b (gradFun (I := I) g u b)
          (gradFun (I := I) g u b))) = 0 := by
  funext b
  have h_ev : u =ᶠ[𝓝 b] (fun _ : M => (0 : ℝ)) := by
    rw [h_u_zero]; rfl
  have h_grad_zero :
      gradFun (I := I) g u b = (0 : TangentSpace I b) :=
    gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
  rw [h_grad_zero]
  have h_map : g.inner b (0 : TangentSpace I b) =
      (0 : TangentSpace I b →L[ℝ] ℝ) := map_zero _
  rw [h_map]
  change Real.sqrt ((0 : TangentSpace I b →L[ℝ] ℝ) (0 : TangentSpace I b)) =
    (0 : M → ℝ) b
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_g_inner_gradFun_eq_zero_of_scalar_zero target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOUActiveFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  have h_integrand_zero :
      (fun b : M => Real.sqrt
          (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b))) = 0 :=
    sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
      (I := I) (M := M) g h_scalar_zero
  rw [h_integrand_zero]
  exact _root_.MeasureTheory.eLpNorm_zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive target :: scope.openDecls } }

end GradUniform

section ChartSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_4 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_4 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_4 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_4 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_5 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_5
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_5 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_5 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_5
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_5 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOUActiveFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact wkpNormChart_zero_fun (I := I) (M := M) (by norm_num : (1 : ℝ≥0∞) ≤ 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive target :: scope.openDecls } }

end ChartSobolev

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
