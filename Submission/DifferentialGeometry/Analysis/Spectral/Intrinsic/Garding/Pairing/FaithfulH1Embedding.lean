import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.SobolevScaleSummability
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Lowering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem oneMinusConnLapSmooth_toL2_inner_eq_h1
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) :
    ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        (v : TensorL2 0 s g)⟫_ℝ =
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩,
        smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨v⟩⟫_ℝ := by
  have h_rhs :
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩,
          smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨v⟩⟫_ℝ =
        ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ +
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, SmoothCcTensorH1.inner_def,
      tensorH1Inner_def]
    rw [show tensorL2Inner (I := I) (M := M) g 0 s
            (⟨T⟩ : SmoothCcTensorH1 g 0 s).toCcTensor.toFun
            (⟨v⟩ : SmoothCcTensorH1 g 0 s).toCcTensor.toFun =
          ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ by
        rw [UniformSpace.Completion.inner_coe]
        exact (SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  have h_dir :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T).toFun
          (covGrad (I := I) (M := M) g 0 s v).toFun :=
    (tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 s T v).symm
  have h_green :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T).toFun
          (covGrad (I := I) (M := M) g 0 s v).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap
      (I := I) (M := M) g s hint T v
  have h_lhs :
      ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
            TensorL2 0 s g),
          (v : TensorL2 0 s g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 s
            (oneMinusConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_split :
      tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmooth (I := I) g 0 s T).toFun v.toFun =
        tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun -
          tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
    have h_coe :
        ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
              TensorL2 0 s g),
            (v : TensorL2 0 s g)⟫_ℝ =
          ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ -
            ⟪((rawTensorConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
                TensorL2 0 s g),
              (v : TensorL2 0 s g)⟫_ℝ := by
      rw [show (oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) =
            T - rawTensorConnLapSmooth (I := I) g 0 s T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
    rw [show ⟪((rawTensorConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
            TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1 ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1

theorem inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : SmoothCcTensor g 0 s) (w : TensorH1Compl g 0 s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩, w⟫_ℝ =
      ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s w⟫_ℝ := by
  set A : TensorH1Compl g 0 s → ℝ :=
    fun w => ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩, w⟫_ℝ with hA
  set B : TensorH1Compl g 0 s → ℝ :=
    fun w => ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s w⟫_ℝ with hB
  have hA_cont : Continuous A := by
    rw [hA]
    exact (innerSL ℝ
      (smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩)).continuous
  have hB_cont : Continuous B := by
    rw [hB]
    exact ((innerSL ℝ
        ((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g)).comp
      (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s)).continuous
  have h_eq_on :
      A ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) =
        B ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) := by
    funext V
    have hcoe : (V : TensorH1Compl g 0 s) =
        smoothToTensorH1Compl (I := I) (M := M) g 0 s V := rfl
    simp only [Function.comp_apply, hA, hB, hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : SmoothCcTensorH1 g 0 s) := by
      cases V; rfl
    rw [hV]
    rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
    rw [← oneMinusConnLapSmooth_toL2_inner_eq_h1
      (I := I) (M := M) g s hint T V.toCcTensor]
  have h_dense :
      DenseRange ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) :=
    UniformSpace.Completion.denseRange_coe
  have h_AB : A = B := h_dense.equalizer hA_cont hB_cont h_eq_on
  exact congr_fun h_AB w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green ``Submission.DifferentialGeometry.Analysis.Spectral.inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green

theorem TensorH1ComplToTensorL2_injective_of_green
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  refine ext_inner_left ℝ ?_
  intro v
  rw [inner_zero_right]
  set A : TensorH1Compl g 0 s → ℝ := fun v => ⟪v, w⟫_ℝ with hA
  have hA_cont : Continuous A := by
    rw [hA]
    exact Continuous.inner continuous_id continuous_const
  have h_eq_on :
      A ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) =
        (fun _ : SmoothCcTensorH1 g 0 s => (0 : ℝ)) := by
    funext V
    simp only [Function.comp_apply, hA]
    have hcoe : (V : TensorH1Compl g 0 s) =
        smoothToTensorH1Compl (I := I) (M := M) g 0 s V := rfl
    rw [hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : SmoothCcTensorH1 g 0 s) := by cases V; rfl
    rw [hV]
    rw [inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green
      (I := I) (M := M) g s hint V.toCcTensor w]
    rw [hw, inner_zero_right]
  have h_dense :
      DenseRange ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq :
      A = (fun _ : TensorH1Compl g 0 s => (0 : ℝ)) :=
    h_dense.equalizer hA_cont continuous_const h_eq_on
  have := congr_fun h_eq v
  rw [hA] at this
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_of_green then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_of_green"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_of_green ``Submission.DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_of_green

theorem TensorH1ComplToTensorL2_injective_two
    (g : SmoothRiemannianMetric I M) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 2) :=
  TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g 2
    (loweringIntertwiner_two (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_two ``Submission.DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_two

theorem TensorH1ComplToTensorL2_injective_three
    (g : SmoothRiemannianMetric I M) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 3) :=
  TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g 3
    (loweringIntertwiner_three (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_three ``Submission.DifferentialGeometry.Analysis.Spectral.TensorH1ComplToTensorL2_injective_three

theorem smoothEigen_h1_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    smoothToTensorH1Compl (I := I) (M := M) g 0 s
        ⟨eigenvectorSmooth (I := I) (M := M) g 0 s i⟩ =
      (i.fst.val)⁻¹ •
        eigenvectorResolvent (I := I) (M := M) g 0 s i := by
  apply TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g s
    (loweringIntertwiner (I := I) (M := M) g s)
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
  change (eigenvectorSmooth (I := I) (M := M) g 0 s i :
        TensorL2 0 s g) =
      TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s
        ((i.fst.val)⁻¹ •
          eigenvectorResolvent (I := I) (M := M) g 0 s i)
  rw [eigenvectorSmooth_toL2 (I := I) (M := M) g 0 s i,
    map_smul]
  exact eigenvector_eq_resolvent_smul (I := I) (M := M) g 0 s i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothEigen_h1_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothEigen_h1_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothEigen_h1_eq ``Submission.DifferentialGeometry.Analysis.Spectral.smoothEigen_h1_eq

theorem smoothToTensorH1Compl_eigenvectorSmooth_eq
    (g : SmoothRiemannianMetric I M)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    smoothToTensorH1Compl (I := I) (M := M) g 0 2
        ⟨eigenvectorSmooth (I := I) (M := M) g 0 2 i⟩ =
      (i.fst.val)⁻¹ •
        eigenvectorResolvent (I := I) (M := M) g 0 2 i := by
  exact smoothEigen_h1_eq (I := I) (M := M) g 2 i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothToTensorH1Compl_eigenvectorSmooth_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothToTensorH1Compl_eigenvectorSmooth_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothToTensorH1Compl_eigenvectorSmooth_eq ``Submission.DifferentialGeometry.Analysis.Spectral.smoothToTensorH1Compl_eigenvectorSmooth_eq

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorEigenIdx_val_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorEigenIdx_val_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorEigenIdx_val_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorEigenIdx_val_pos ``Submission.DifferentialGeometry.Analysis.Spectral.tensorEigenIdx_val_pos

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem one_add_lambda_eq_inv_val
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s) :
    1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) i = (i.fst.val)⁻¹ := by
  have hpos : 0 < i.fst.val := tensorEigenIdx_val_pos (I := I) (M := M) i
  change 1 + tensorLaplacianEigenvalueOf i.fst.val = (i.fst.val)⁻¹
  rw [tensorLaplacianEigenvalueOf]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.one_add_lambda_eq_inv_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.one_add_lambda_eq_inv_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.one_add_lambda_eq_inv_val ``Submission.DifferentialGeometry.Analysis.Spectral.one_add_lambda_eq_inv_val

theorem oneMinus_coeff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 s))
    (T : SmoothCcTensor g 0 s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 s T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  classical
  have hb :
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact i =
        (eigenvectorSmooth (I := I) (M := M) g 0 s i :
          TensorL2 0 s g) := by
    rw [tensorResolventHilbertEigenbasisSigma_apply,
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 s i]
  rw [tensorL2Coeff_eq_inner, tensorL2Coeff_eq_inner, hb,
    SmoothCcTensor.toL2_apply, SmoothCcTensor.toL2_apply]
  rw [real_inner_comm
    ((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
      TensorL2 0 s g)
    (eigenvectorSmooth (I := I) (M := M) g 0 s i : TensorL2 0 s g),
    oneMinusConnLapSmooth_toL2_inner_eq_h1 (I := I) (M := M) g s
      (loweringIntertwiner (I := I) (M := M) g s) T
      (eigenvectorSmooth (I := I) (M := M) g 0 s i)]
  rw [smoothEigen_h1_eq (I := I) (M := M) g s i,
    inner_smul_right]
  rw [real_inner_comm
    (eigenvectorResolvent (I := I) (M := M) g 0 s i)
    (smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩),
    eigenvectorSmooth_weak_eigen (I := I) (M := M) g 0 s i ⟨T⟩]
  rw [show ((⟨T⟩ : SmoothCcTensorH1 g 0 s).toCcTensor : TensorL2 0 s g) =
        (T : TensorL2 0 s g) from rfl,
    real_inner_comm
      (eigenvectorSmooth (I := I) (M := M) g 0 s i : TensorL2 0 s g)
      (T : TensorL2 0 s g),
    one_add_lambda_eq_inv_val (I := I) (M := M) i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinus_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinus_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinus_coeff ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinus_coeff

theorem rawLap_coeff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 s))
    (T : SmoothCcTensor g 0 s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 s T)) i =
      (- Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  have h_split :
      rawTensorConnLapSmooth (I := I) g 0 s T =
        T - oneMinusConnLapSmooth (I := I) g 0 s T := by
    rw [show oneMinusConnLapSmooth (I := I) g 0 s T =
          T - rawTensorConnLapSmooth (I := I) g 0 s T from rfl]
    abel
  rw [h_split, map_sub, tensorL2Coeff_eq_inner, inner_sub_right,
    ← tensorL2Coeff_eq_inner, ← tensorL2Coeff_eq_inner,
    oneMinus_coeff (I := I) (M := M) g s h_compact T i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.rawLap_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.rawLap_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.rawLap_coeff ``Submission.DifferentialGeometry.Analysis.Spectral.rawLap_coeff

theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  exact oneMinus_coeff (I := I) (M := M) g 2 h_compact T i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmooth ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmooth

theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) (k : ℕ) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ k *
        tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
          (I := I) (M := M) g h_compact (oneMinusConnLapSmoothIter (I := I) g 0 2 k T) i,
        ih, pow_succ]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter

theorem smoothCcTensor_tensorL2Coeff_weighted_summable_even
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
        (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  have h_term :
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 T) i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2
            (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i) ^ 2 := by
    funext i
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
      (I := I) (M := M) g h_compact T i k]
    rw [mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [h_term]
  have h_parseval := tensorParseval_l2Coeff_ofCompact_sq
    (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))
  exact tensorL2Coeff_summable_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable_even then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable_even"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable_even ``Submission.DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable_even

theorem smoothCcTensor_tensorL2Coeff_weighted_summable
    (g : SmoothRiemannianMetric I M) (a : ℝ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i a *
        (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (a / 2)
  have hak : a ≤ (2 * k : ℕ) := by
    have : a / 2 ≤ (k : ℝ) := hk
    push_cast
    linarith
  exact summable_tensorSobolevWeight_of_even
    (I := I) (M := M)
    (fun i => tensorL2Coeff (I := I) (M := M) h_compact
      (SmoothCcTensor.toL2 T) i)
    hak
    (smoothCcTensor_tensorL2Coeff_weighted_summable_even
      (I := I) (M := M) g k T h_compact)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable ``Submission.DifferentialGeometry.Analysis.Spectral.smoothCcTensor_tensorL2Coeff_weighted_summable

end Spectral
end Analysis
end DifferentialGeometry

end
