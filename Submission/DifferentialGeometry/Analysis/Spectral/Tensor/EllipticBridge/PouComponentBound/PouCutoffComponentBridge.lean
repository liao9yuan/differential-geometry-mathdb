import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransitionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

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

def chartPushedPouWeight (α : M) : EuclN → ℝ :=
  chartPushedRaw I α (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedPouWeight_abs_le_one (α : M) (y : EuclN) :
    |chartPushedPouWeight (I := I) (M := M) α y| ≤ 1 := by
  classical
  unfold chartPushedPouWeight
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    set x : M := (extChartAt I α).symm (toEuclidean.symm y) with hx_def
    have h_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (chartAtlasPOU I M).nonneg α x
    have h_le : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (chartAtlasPOU I M).le_one α x
    rw [abs_of_nonneg h_nn]
    exact h_le
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy, abs_zero]
    exact zero_le_one

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_abs_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_abs_le_one target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedPouWeight_norm_le_one (α : M) (y : EuclN) :
    ‖chartPushedPouWeight (I := I) (M := M) α y‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact chartPushedPouWeight_abs_le_one (I := I) (M := M) α y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_norm_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_norm_le_one target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma chartPushedPouWeight_measurable (α : M) :
    Measurable (chartPushedPouWeight (I := I) (M := M) α) := by
  classical
  unfold chartPushedPouWeight
  exact chartPushedRaw_measurable (I := I) (M := M) α
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_measurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_measurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_measurable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_measurable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedPouWeight_aestronglyMeasurable (α : M) :
    AEStronglyMeasurable (chartPushedPouWeight (I := I) (M := M) α)
      (chartLebesgueMeasure (I := I) (M := M) α) :=
  (chartPushedPouWeight_measurable (I := I) (M := M) α).aestronglyMeasurable

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_aestronglyMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_aestronglyMeasurable target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedPouWeight_mul_memLp
    (α : M) {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    MemLp (fun y => chartPushedPouWeight (I := I) (M := M) α y * f y) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  refine ⟨(chartPushedPouWeight_aestronglyMeasurable
    (I := I) (M := M) α).mul hf.1, ?_⟩
  have hpt : ∀ y : EuclN,
      ‖chartPushedPouWeight (I := I) (M := M) α y * f y‖ ≤ ‖f y‖ := by
    intro y
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right
      (chartPushedPouWeight_norm_le_one (I := I) (M := M) α y)
      (norm_nonneg _)).trans ?_
    rw [one_mul]
  calc _root_.MeasureTheory.eLpNorm (fun y => chartPushedPouWeight (I := I) (M := M) α y * f y) 2
        (chartLebesgueMeasure (I := I) (M := M) α)
      ≤ _root_.MeasureTheory.eLpNorm f 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
        _root_.MeasureTheory.eLpNorm_mono hpt
    _ < ⊤ := hf.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_mul_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedPouWeight_mul_memLp target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma eLpNorm_chartPushedPouWeight_mul_le
    (α : M) (f : EuclN → ℝ) :
    eLpNorm (fun y => chartPushedPouWeight (I := I) (M := M) α y * f y) 2
        (chartLebesgueMeasure (I := I) (M := M) α) ≤
      eLpNorm f 2 (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  have hpt : ∀ y : EuclN,
      ‖chartPushedPouWeight (I := I) (M := M) α y * f y‖ ≤ ‖f y‖ := by
    intro y
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right
      (chartPushedPouWeight_norm_le_one (I := I) (M := M) α y)
      (norm_nonneg _)).trans ?_
    rw [one_mul]
  exact _root_.MeasureTheory.eLpNorm_mono hpt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushedPouWeight_mul_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushedPouWeight_mul_le target :: scope.openDecls } }

private def boundedPouMulLp
    (α : M) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (chartPushedPouWeight_mul_memLp (I := I) (M := M) α (Lp.memLp f)).toLp
    (fun y => chartPushedPouWeight (I := I) (M := M) α y *
      (f : EuclN → ℝ) y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma boundedPouMulLp_coeFn
    (α : M) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    ((boundedPouMulLp (I := I) (M := M) α f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      fun y => chartPushedPouWeight (I := I) (M := M) α y *
        (f : EuclN → ℝ) y := by
  unfold boundedPouMulLp
  exact MemLp.coeFn_toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp_coeFn target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma boundedPouMulLp_add
    (α : M) (f₁ f₂ : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    boundedPouMulLp (I := I) (M := M) α (f₁ + f₂) =
      boundedPouMulLp (I := I) (M := M) α f₁ +
        boundedPouMulLp (I := I) (M := M) α f₂ := by
  classical
  apply Lp.ext
  refine (boundedPouMulLp_coeFn (I := I) (M := M) α (f₁ + f₂)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  filter_upwards [Lp.coeFn_add f₁ f₂,
    boundedPouMulLp_coeFn (I := I) (M := M) α f₁,
    boundedPouMulLp_coeFn (I := I) (M := M) α f₂] with y hy_add hy₁ hy₂
  rw [Pi.add_apply, hy₁, hy₂, hy_add, Pi.add_apply, mul_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp_add target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma boundedPouMulLp_smul
    (α : M) (c : ℝ) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    boundedPouMulLp (I := I) (M := M) α (c • f) =
      c • boundedPouMulLp (I := I) (M := M) α f := by
  classical
  apply Lp.ext
  refine (boundedPouMulLp_coeFn (I := I) (M := M) α (c • f)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul c _).symm
  filter_upwards [Lp.coeFn_smul c f,
    boundedPouMulLp_coeFn (I := I) (M := M) α f] with y hy_smul hy
  rw [Pi.smul_apply, hy, hy_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_left_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLp_smul target :: scope.openDecls } }

private def boundedPouMulLpLin (α : M) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) →ₗ[ℝ]
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) where
  toFun f := boundedPouMulLp (I := I) (M := M) α f
  map_add' f₁ f₂ := boundedPouMulLp_add (I := I) (M := M) α f₁ f₂
  map_smul' c f := boundedPouMulLp_smul (I := I) (M := M) α c f

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpLin target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] private lemma boundedPouMulLpLin_apply
    (α : M) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    boundedPouMulLpLin (I := I) (M := M) α f =
      boundedPouMulLp (I := I) (M := M) α f := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpLin_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpLin_apply target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma boundedPouMulLpLin_norm_le
    (α : M) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    ‖boundedPouMulLpLin (I := I) (M := M) α f‖ ≤ 1 * ‖f‖ := by
  classical
  rw [one_mul, boundedPouMulLpLin_apply]
  unfold boundedPouMulLp
  rw [MeasureTheory.Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  exact eLpNorm_chartPushedPouWeight_mul_le (I := I) (M := M) α _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpLin_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpLin_norm_le target :: scope.openDecls } }

def boundedPouMulLpCLM (α : M) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) →L[ℝ]
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (boundedPouMulLpLin (I := I) (M := M) α).mkContinuous 1
    (boundedPouMulLpLin_norm_le (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] private lemma boundedPouMulLpCLM_apply
    (α : M) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    boundedPouMulLpCLM (I := I) (M := M) α f =
      boundedPouMulLp (I := I) (M := M) α f := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM_apply target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma boundedPouMulLpCLM_coeFn
    (α : M) (f : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    ((boundedPouMulLpCLM (I := I) (M := M) α f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      fun y => chartPushedPouWeight (I := I) (M := M) α y *
        (f : EuclN → ℝ) y := by
  rw [boundedPouMulLpCLM_apply]
  exact boundedPouMulLp_coeFn (I := I) (M := M) α f

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.boundedPouMulLpCLM_coeFn target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pou_smul_eq_pou_smul_cutoff_smul
    (α : M) (x : M) (v : ℝ) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v) := by
  classical
  by_cases hρ : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρ, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
  · have hx_support : x ∈
        tsupport
          (fun y : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hρ
    have hχ : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) α hx_support
    rw [hχ, one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_smul_eq_pou_smul_cutoff_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pou_smul_eq_pou_smul_cutoff_smul target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponentPou_eq_pou_mul_cutoffComponentScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (x : M) :
    tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
  classical
  unfold tensorChartComponentPou cutoffComponentScalar
  exact pou_smul_eq_pou_smul_cutoff_smul (I := I) (M := M) α x
    (tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentPou_eq_pou_mul_cutoffComponentScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentPou_eq_pou_mul_cutoffComponentScalar target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedRaw_pou_mul_eq_chartPushedPouWeight_mul
    (α : M) (F : M → ℝ) (y : EuclN) :
    chartPushedRaw I α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * F x)
        y =
      chartPushedPouWeight (I := I) (M := M) α y *
        chartPushedRaw I α F y := by
  classical
  unfold chartPushedPouWeight
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_eq_chartPushedPouWeight_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_eq_chartPushedPouWeight_mul target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_eq_chartPushedPouWeight_mul_cutoffComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 y =
      chartPushedPouWeight (I := I) (M := M) α y *
        cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y := by
  classical
  rw [tensorChartComponent_def, cutoffComponentEuclid_eq_chartPushedRaw]
  have h_scalar :
      tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
    funext x
    exact tensorChartComponentPou_eq_pou_mul_cutoffComponentScalar
      (I := I) (M := M) g r s S α P₀ x
  rw [h_scalar]
  exact chartPushedRaw_pou_mul_eq_chartPushedPouWeight_mul (I := I) (M := M) α
    (cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedPouWeight_mul_cutoffComponentEuclid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedPouWeight_mul_cutoffComponentEuclid target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      boundedPouMulLpCLM (I := I) (M := M) α
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (S : TensorL2 r s g) α P₀) := by
  classical
  apply Lp.ext
  refine (tensorL2ChartComponent_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀).trans ?_
  refine Filter.EventuallyEq.symm (Filter.EventuallyEq.trans
    (boundedPouMulLpCLM_coeFn (I := I) (M := M) α
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀)) ?_)
  filter_upwards [tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀] with y hy
  rw [hy]
  exact (tensorChartComponent_eq_chartPushedPouWeight_mul_cutoffComponentEuclid
    (I := I) (M := M) g r s S α P₀ y).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_boundedPouMul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      boundedPouMulLpCLM (I := I) (M := M) α
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)) := by
  classical
  have h_fun :
      (fun u : TensorL2 r s g =>
        boundedPouMulLpCLM (I := I) (M := M) α
          (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)) =
        (fun u : TensorL2 r s g =>
          boundedPouMulLpCLM (I := I) (M := M) α
            (tensorL2ChartComponentCutoffCLM (I := I) (M := M)
              g r s α P₀ u)) := by
    funext u
    rw [tensorL2ChartComponentCutoffCLM_apply]
  rw [h_fun]
  exact (boundedPouMulLpCLM (I := I) (M := M) α).continuous.comp
    (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_boundedPouMul_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_boundedPouMul_cutoff target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponent_eq_boundedPouMul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ =
      boundedPouMulLpCLM (I := I) (M := M) α
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀) := by
  classical
  set lhs : TensorL2 r s g → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    fun v => tensorL2ChartComponent (I := I) (M := M) g r s v α P₀
    with hlhs_def
  set rhs : TensorL2 r s g → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    fun v => boundedPouMulLpCLM (I := I) (M := M) α
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀)
    with hrhs_def
  suffices h_eq : lhs = rhs by
    exact congrFun h_eq u
  have h_lhs_cont : Continuous lhs := by
    rw [hlhs_def]
    exact continuous_tensorL2ChartComponent (I := I) (M := M) g r s α P₀
  have h_rhs_cont : Continuous rhs := by
    rw [hrhs_def]
    exact continuous_boundedPouMul_cutoff (I := I) (M := M) g r s α P₀
  have h_denseRange :
      DenseRange ((↑) : SmoothCcTensor g r s → TensorL2 r s g) :=
    UniformSpace.Completion.denseRange_coe
  refine h_denseRange.equalizer h_lhs_cont h_rhs_cont ?_
  funext S
  rw [Function.comp_apply, Function.comp_apply, hlhs_def, hrhs_def]
  exact tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff
    (I := I) (M := M) g r s S α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_eq_boundedPouMul_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_eq_boundedPouMul_cutoff target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y => chartPushedRaw I α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  rw [tensorL2ChartComponent_eq_boundedPouMul_cutoff (I := I) (M := M)
    g r s u α P₀]
  exact boundedPouMulLpCLM_coeFn (I := I) (M := M) α
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_ae_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y => chartPushedRaw I α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y) := by
  classical
  refine (tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s u α P₀).trans ?_
  filter_upwards [tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀] with y hy
  rw [hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_eq_pou_transport_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_eq_pou_transport_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_eq_pou_transport_sum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_eq_pou_transport_sum

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
