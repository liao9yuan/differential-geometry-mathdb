import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.TensorChartComponentSobolev.PerAlphaGradIntrinsic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace HebeyBlock

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma exists_perAlphaSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C_grad, hC_grad_nn, hC_grad_bound⟩ :=
    tensorChartComponentScalar_grad_eLpNorm_le
      (I := I) (M := M) g r s
  exact tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
    (I := I) (M := M) g r s α hC_grad_nn
    (fun S Idx Jdx => hC_grad_bound S α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.exists_perAlphaSobolevConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.exists_perAlphaSobolevConstant target :: scope.openDecls } }

private noncomputable def perAlphaSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose
    (exists_perAlphaSobolevConstant (I := I) (M := M) g r s α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perAlphaSobolevConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaSobolevConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec
    (exists_perAlphaSobolevConstant
      (I := I) (M := M) g r s α)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant_intrinsic_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant_intrinsic_nonneg target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perAlphaSobolevConstant_intrinsic_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) ≤
      ENNReal.ofReal
          (perAlphaSobolevConstant (I := I) (M := M) g r s α) *
        (‖S‖₊ : ℝ≥0∞) :=
  (Classical.choose_spec
    (exists_perAlphaSobolevConstant
      (I := I) (M := M) g r s α)).2 S Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant_intrinsic_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant_intrinsic_bound target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive_intrinsic
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
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive_intrinsic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive_intrinsic target :: scope.openDecls } }

private noncomputable def totalActiveSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOUActiveFinset I M,
    perAlphaSobolevConstant (I := I) (M := M) g r s α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveSobolevConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveSobolevConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma totalActiveSobolevConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveSobolevConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveSobolevConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaSobolevConstant_intrinsic_nonneg (I := I) (M := M) g r s α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveSobolevConstant_intrinsic_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveSobolevConstant_intrinsic_nonneg target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perAlphaSobolevConstant_le_totalActiveSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOUActiveFinset I M) :
    perAlphaSobolevConstant (I := I) (M := M) g r s α ≤
      totalActiveSobolevConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveSobolevConstant
  have h_split :
      ∑ β ∈ chartAtlasPOUActiveFinset I M,
        perAlphaSobolevConstant (I := I) (M := M) g r s β =
        perAlphaSobolevConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOUActiveFinset I M).erase α,
          perAlphaSobolevConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOUActiveFinset I M).erase α,
            perAlphaSobolevConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaSobolevConstant_intrinsic_nonneg (I := I) (M := M) g r s β)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant_le_totalActiveSobolevConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaSobolevConstant_le_totalActiveSobolevConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem tensorChartComponent_wkpNormChart_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  refine ⟨totalActiveSobolevConstant (I := I) (M := M) g r s,
    totalActiveSobolevConstant_intrinsic_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOUActiveFinset I M
  · have h_per :
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal
              (perAlphaSobolevConstant (I := I) (M := M) g r s α) *
            (‖S‖₊ : ℝ≥0∞) :=
      perAlphaSobolevConstant_intrinsic_bound
        (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal
            (perAlphaSobolevConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal
            (totalActiveSobolevConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaSobolevConstant_le_totalActiveSobolevConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal
              (perAlphaSobolevConstant (I := I) (M := M) g r s α) *
              (‖S‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal
              (totalActiveSobolevConstant (I := I) (M := M) g r s) *
              (‖S‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le)
    exact h_per.trans h_envelope_le
  · rw [wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive_intrinsic
      (I := I) (M := M) g r s hα S.toCcTensor Idx Jdx]
    exact zero_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponent_wkpNormChart_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponent_wkpNormChart_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponent_wkpNormChart_le ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponent_wkpNormChart_le

end HebeyBlock
end Sobolev
end Analysis
end DifferentialGeometry

end
