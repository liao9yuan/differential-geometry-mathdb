import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.TensorChartComponentSobolev.PerChartGradientL2Headline
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponent.SobolevBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive_intrinsic
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
  classical
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
                g r s S α Idx Jdx) b))) = 0 := by
    funext b
    have h_ev :
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
          =ᶠ[𝓝 b] (fun _ : M => (0 : ℝ)) := by
      rw [h_scalar_zero]; rfl
    have h_grad_zero :
        gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b =
          (0 : TangentSpace I b) :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    rw [h_grad_zero]
    have h_map : g.inner b (0 : TangentSpace I b) =
        (0 : TangentSpace I b →L[ℝ] ℝ) := map_zero _
    rw [h_map]
    change Real.sqrt ((0 : TangentSpace I b →L[ℝ] ℝ) (0 : TangentSpace I b)) =
      (0 : M → ℝ) b
    simp
  rw [h_integrand_zero]
  exact _root_.MeasureTheory.eLpNorm_zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive_intrinsic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive_intrinsic target :: scope.openDecls } }

private noncomputable def perAlphaGradConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perAlphaGradConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaGradConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant_intrinsic_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant_intrinsic_nonneg target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perAlphaGradConstant_intrinsic_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (perAlphaGradConstant (I := I) (M := M) g r s α) *
        (‖S‖₊ : ℝ≥0∞) :=
  (Classical.choose_spec
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α)).2 S Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant_intrinsic_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant_intrinsic_bound target :: scope.openDecls } }

private noncomputable def totalActiveGradConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOUActiveFinset I M,
    perAlphaGradConstant (I := I) (M := M) g r s α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveGradConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveGradConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma totalActiveGradConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveGradConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveGradConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaGradConstant_intrinsic_nonneg (I := I) (M := M) g r s α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveGradConstant_intrinsic_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.totalActiveGradConstant_intrinsic_nonneg target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perAlphaGradConstant_le_totalActiveGradConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOUActiveFinset I M) :
    perAlphaGradConstant (I := I) (M := M) g r s α ≤
      totalActiveGradConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveGradConstant
  have h_split :
      ∑ β ∈ chartAtlasPOUActiveFinset I M,
        perAlphaGradConstant (I := I) (M := M) g r s β =
        perAlphaGradConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOUActiveFinset I M).erase α,
          perAlphaGradConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOUActiveFinset I M).erase α,
            perAlphaGradConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaGradConstant_intrinsic_nonneg (I := I) (M := M) g r s β)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant_le_totalActiveGradConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.perAlphaGradConstant_le_totalActiveGradConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem tensorChartComponentScalar_grad_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C_grad : ℝ, 0 ≤ C_grad ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C_grad * (‖S‖₊ : ℝ≥0∞) := by
  classical
  refine ⟨totalActiveGradConstant (I := I) (M := M) g r s,
    totalActiveGradConstant_intrinsic_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOUActiveFinset I M
  · have h_per :
        _root_.MeasureTheory.eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal
              (perAlphaGradConstant (I := I) (M := M) g r s α) *
            (‖S‖₊ : ℝ≥0∞) :=
      perAlphaGradConstant_intrinsic_bound (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal
            (perAlphaGradConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal
            (totalActiveGradConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaGradConstant_le_totalActiveGradConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal
              (perAlphaGradConstant (I := I) (M := M) g r s α) *
              (‖S‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal
              (totalActiveGradConstant (I := I) (M := M) g r s) *
              (‖S‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le)
    exact h_per.trans h_envelope_le
  · rw [eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive_intrinsic
      (I := I) (M := M) g r s hα S.toCcTensor Idx Jdx]
    exact zero_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponentScalar_grad_eLpNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponentScalar_grad_eLpNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponentScalar_grad_eLpNorm_le ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorChartComponentScalar_grad_eLpNorm_le

end HebeyBlock
end Sobolev
end Analysis
end DifferentialGeometry

end
