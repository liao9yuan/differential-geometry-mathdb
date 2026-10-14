import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode.L2
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Spectral.Synthesis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

def solutionModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  perModeConvolutionL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.solutionModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.solutionModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.solutionModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.solutionModeCoeff

def derivModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  perModeConvolutionDerivL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.derivModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.derivModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.derivModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.derivModeCoeff

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_solutionModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      T * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  rw [solutionModeCoeff, perModeConvolutionL2_apply]
  exact norm_perModeConvolutionL2Fun_le (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_solutionModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_solutionModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_solutionModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_solutionModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
theorem lambda_mul_norm_solutionModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorEigenIdx.lambda (I := I) (M := M) i *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  have hbase := perModeConvolutionL2_sq_le (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (tensor_lambda_nonneg (I := I) (M := M) i)] at hbase
  exact hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.lambda_mul_norm_solutionModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.lambda_mul_norm_solutionModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.lambda_mul_norm_solutionModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.lambda_mul_norm_solutionModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
theorem one_add_lambda_mul_norm_solutionModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  have h1 := norm_solutionModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have h2 := lambda_mul_norm_solutionModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have hexpand : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖
      = ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ +
        TensorEigenIdx.lambda (I := I) (M := M) i *
          ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ := by ring
  rw [hexpand]
  calc ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ +
        TensorEigenIdx.lambda (I := I) (M := M) i *
          ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖
      ≤ T * ‖timeModeCoeff (I := I) (M := M) f i‖ +
          ‖timeModeCoeff (I := I) (M := M) f i‖ := by gcongr
    _ = (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_norm_solutionModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_norm_solutionModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_norm_solutionModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_norm_solutionModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
theorem sqrt_lambda_mul_norm_solutionModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Real.sqrt (TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set φ := ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ with hφ_def
  set ff := ‖timeModeCoeff (I := I) (M := M) f i‖ with hff_def
  have hφ_nn : 0 ≤ φ := norm_nonneg _
  have hff_nn : 0 ≤ ff := norm_nonneg _
  have h1 : φ ≤ T * ff := norm_solutionModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have h2 : lam * φ ≤ ff :=
    lambda_mul_norm_solutionModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have hlhs_nn : 0 ≤ Real.sqrt lam * φ :=
    mul_nonneg (Real.sqrt_nonneg _) hφ_nn
  have hrhs_nn : 0 ≤ Real.sqrt T * ff :=
    mul_nonneg (Real.sqrt_nonneg _) hff_nn
  have hsqL : (Real.sqrt lam * φ) ^ 2 = lam * φ * φ := by
    rw [mul_pow, Real.sq_sqrt hlam_nn]; ring
  have hsqR : (Real.sqrt T * ff) ^ 2 = T * ff * ff := by
    rw [mul_pow, Real.sq_sqrt hT]; ring
  have hsq_le : (Real.sqrt lam * φ) ^ 2 ≤ (Real.sqrt T * ff) ^ 2 := by
    rw [hsqL, hsqR]
    calc lam * φ * φ ≤ ff * φ := mul_le_mul_of_nonneg_right h2 hφ_nn
      _ ≤ ff * (T * ff) := mul_le_mul_of_nonneg_left h1 hff_nn
      _ = T * ff * ff := by ring
  nlinarith [hsq_le, hlhs_nn, hrhs_nn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.sqrt_lambda_mul_norm_solutionModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.sqrt_lambda_mul_norm_solutionModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.sqrt_lambda_mul_norm_solutionModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.sqrt_lambda_mul_norm_solutionModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
theorem one_add_lambda_sqrt_mul_norm_solutionModeCoeff_le (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (1 / 2 : ℝ) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ≤
      2 * Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_nn : (0 : ℝ) ≤ 1 + lam := by linarith
  set φ := ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ with hφ_def
  set ff := ‖timeModeCoeff (I := I) (M := M) f i‖ with hff_def
  have hφ_nn : 0 ≤ φ := norm_nonneg _
  have hff_nn : 0 ≤ ff := norm_nonneg _
  have hsqrt_le : (1 + lam) ^ (1 / 2 : ℝ) ≤ 1 + Real.sqrt lam := by
    have hrw : (1 + lam) ^ (1 / 2 : ℝ) = Real.sqrt (1 + lam) := by
      rw [Real.sqrt_eq_rpow]
    rw [hrw]
    have hsl_nn : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ 1 + Real.sqrt lam := by linarith
    have hsl_sq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam_nn
    rw [show (1 + Real.sqrt lam) = Real.sqrt ((1 + Real.sqrt lam) ^ 2) from
      (Real.sqrt_sq hrhs_nn).symm]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [hsl_nn, hsl_sq]
  have hconv : φ ≤ Real.sqrt T * ff := by
    have hTle : T ≤ Real.sqrt T := by
      have hsqrt_ge : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
      have hsqrt_le_one : Real.sqrt T ≤ 1 :=
        Real.sqrt_le_one.mpr hT1
      nlinarith [Real.sqrt_nonneg T, hsqrt_ge, hsqrt_le_one]
    calc φ ≤ T * ff := norm_solutionModeCoeff_le (I := I) (M := M) (a := a) hT.le f i
      _ ≤ Real.sqrt T * ff := mul_le_mul_of_nonneg_right hTle hff_nn
  have hhalf : Real.sqrt lam * φ ≤ Real.sqrt T * ff :=
    sqrt_lambda_mul_norm_solutionModeCoeff_le (I := I) (M := M) (a := a) hT.le f i
  calc (1 + lam) ^ (1 / 2 : ℝ) * φ
      ≤ (1 + Real.sqrt lam) * φ := mul_le_mul_of_nonneg_right hsqrt_le hφ_nn
    _ = φ + Real.sqrt lam * φ := by ring
    _ ≤ Real.sqrt T * ff + Real.sqrt T * ff := by gcongr
    _ = 2 * Real.sqrt T * ff := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_sqrt_mul_norm_solutionModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_sqrt_mul_norm_solutionModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_sqrt_mul_norm_solutionModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_sqrt_mul_norm_solutionModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_derivModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      2 * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
  perModeConvolutionDerivL2_sq_le (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_derivModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_derivModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_derivModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_derivModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorSobolevWeight_add_two
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + 2) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight, Real.rpow_add hbase_pos,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorSobolevWeight_add_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorSobolevWeight_add_two target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem weighted_solutionModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (a + 2) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
      (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  have hperMode := one_add_lambda_mul_norm_solutionModeCoeff_le (I := I) (M := M)
    (a := a) hT f i
  have hwa_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hlam_nonneg : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hsol_nonneg : 0 ≤ ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
    norm_nonneg _
  have hsq : ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2 ≤
      ((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
    have hrhs_nonneg : 0 ≤ (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    have hlhs_nonneg : 0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
      mul_nonneg hlam_nonneg hsol_nonneg
    nlinarith [hperMode, hlhs_nonneg, hrhs_nonneg]
  calc tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          (((1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
            ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2) := by
        rw [tensorSobolevWeight_add_two (I := I) (M := M) i a]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          (((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorSobolevWeight_add_one
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + 1) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight, Real.rpow_add hbase_pos,
    Real.rpow_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorSobolevWeight_add_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorSobolevWeight_add_one target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem weighted_solutionModeCoeff_Ha1_le (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ^ 2 ≤
      (2 * Real.sqrt T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_nn : (0 : ℝ) ≤ 1 + lam := by linarith
  have hperMode := one_add_lambda_sqrt_mul_norm_solutionModeCoeff_le (I := I) (M := M)
    (a := a) hT hT1 f i
  have hwa_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsol_nonneg : 0 ≤ ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ :=
    norm_nonneg _
  have hweight_sq : (1 + lam) = ((1 + lam) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + lam) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hbase_nn]
    norm_num
  have hsq : ((1 + lam) ^ (1 / 2 : ℝ) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖) ^ 2 ≤
      (2 * Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
    have hlhs_nonneg : 0 ≤ (1 + lam) ^ (1 / 2 : ℝ) *
        ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ :=
      mul_nonneg (Real.rpow_nonneg hbase_nn _) hsol_nonneg
    have hrhs_nonneg : 0 ≤ 2 * Real.sqrt T *
        ‖timeModeCoeff (I := I) (M := M) f i‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    nlinarith [hperMode, hlhs_nonneg, hrhs_nonneg]
  calc tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          (((1 + lam) ^ (1 / 2 : ℝ) *
            ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖) ^ 2) := by
        rw [tensorSobolevWeight_add_one (I := I) (M := M) i a, hlam_def]
        rw [mul_pow]
        rw [← hweight_sq]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((2 * Real.sqrt T *
            ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = (2 * Real.sqrt T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_Ha1_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_Ha1_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_Ha1_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_solutionModeCoeff_Ha1_le

omit [NeZero (Module.finrank ℝ E)] in
theorem summable_solutionModeCoeff_Ha1 (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      ‖solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ^ 2) := by
  have hdom : Summable (fun i => (2 * Real.sqrt T) ^ 2 *
      (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1))
      (sq_nonneg _)
  · exact weighted_solutionModeCoeff_Ha1_le (I := I) (M := M) (a := a) hT hT1 f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff_Ha1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff_Ha1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff_Ha1 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff_Ha1

omit [NeZero (Module.finrank ℝ E)] in
theorem summable_solutionModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 2) *
      ‖solutionModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2) := by
  have hdom : Summable (fun i => (1 + T) ^ 2 *
      (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2))
      (sq_nonneg _)
  · exact weighted_solutionModeCoeff_le (I := I) (M := M) (a := a) hT f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_solutionModeCoeff

omit [NeZero (Module.finrank ℝ E)] in
theorem weighted_derivModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i a *
        ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
      2 ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  have hbase := norm_derivModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have hwa_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsq : ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
      2 ^ 2 * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
    nlinarith [hbase, norm_nonneg (derivModeCoeff (I := I) (M := M) (a := a) hT f i),
      norm_nonneg (timeModeCoeff (I := I) (M := M) f i)]
  calc tensorSobolevWeight (I := I) (M := M) i a *
          ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i a *
          (2 ^ 2 * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = 2 ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_derivModeCoeff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_derivModeCoeff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_derivModeCoeff_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weighted_derivModeCoeff_le

omit [NeZero (Module.finrank ℝ E)] in
theorem summable_derivModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i a *
      ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2) := by
  have hdom : Summable (fun i => 2 ^ 2 *
      (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a)
      (sq_nonneg _)
  · exact weighted_derivModeCoeff_le (I := I) (M := M) (a := a) hT f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_derivModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_derivModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_derivModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_derivModeCoeff

def maximalRegularityDerivField (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (TensorHs (I := I) (M := M) g r s a) T :=
  timeL2OfModes (I := I) (M := M)
    (fun i => derivModeCoeff (I := I) (M := M) (a := a) hT f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDerivField_timeModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularityDerivField (I := I) (M := M) a hT f) i =
      derivModeCoeff (I := I) (M := M) (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) _
    (summable_derivModeCoeff (I := I) (M := M) (a := a) hT h_compact f) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField_timeModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField_timeModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField_timeModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityDerivField_timeModeCoeff

def maximalRegularitySolutionField (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T :=
  timeL2OfModes (I := I) (M := M)
    (fun i => solutionModeCoeff (I := I) (M := M) (a := a) hT f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionField_timeModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularitySolutionField (I := I) (M := M) a hT f) i =
      solutionModeCoeff (I := I) (M := M) (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) _
    (summable_solutionModeCoeff (I := I) (M := M) (a := a) hT h_compact f) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField_timeModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField_timeModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField_timeModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionField_timeModeCoeff

def maximalRegularitySolutionFieldHa1 (a : ℝ) {T : ℝ} (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T :=
  timeL2OfModes (I := I) (M := M) (σ := a + 1)
    (fun i => solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionFieldHa1_timeModeCoeff (hT : 0 < T)
    (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT f) i =
      solutionModeCoeff (I := I) (M := M) (a := a) hT.le f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a + 1) _
    (summable_solutionModeCoeff_Ha1 (I := I) (M := M) (a := a) hT hT1
      h_compact f) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_timeModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_timeModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_timeModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_timeModeCoeff

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionFieldHa1_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT f‖ ≤
      2 * Real.sqrt T * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M) (b := a + 1)
    h_compact (C := 2 * Real.sqrt T)
    (by positivity) _ f (fun i => ?_)
  rw [maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 f i]
  exact weighted_solutionModeCoeff_Ha1_le (I := I) (M := M) (a := a) hT hT1 f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_norm_le

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionFieldHa1_add (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT (f + f') =
      maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT f +
        maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 f i,
    maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 f' i]
  rw [solutionModeCoeff, solutionModeCoeff, solutionModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_add ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_add

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolutionFieldHa1_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT (f - f') =
      maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT f -
        maximalRegularitySolutionFieldHa1 (I := I) (M := M) a hT f' := by
  have hadd := maximalRegularitySolutionFieldHa1_add (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularitySolutionFieldHa1_sub

def maximalRegularityOp (a : ℝ) {T : ℝ} (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    timeH1 (TensorHs (I := I) (M := M) g r s a) T :=
  TimeSobolev.timeH1.mk (0 : TensorHs (I := I) (M := M) g r s a)
    (maximalRegularityDerivField (I := I) (M := M) a hT.le f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_trace0_eq
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityOp (I := I) (M := M) a hT f) =
      0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_timeDeriv
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT f) =
      maximalRegularityDerivField (I := I) (M := M) a hT.le f :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_timeDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_timeDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_timeDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_timeDeriv

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_trace0 (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityOp (I := I) (M := M) a hT f) = 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_trace0

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_norm_Ha2_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularitySolutionField (I := I) (M := M) a hT.le f‖ ≤
      (1 + T) * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M) (b := a + 2)
    h_compact (C := 1 + T) (by linarith [hT.le]) _ f (fun i => ?_)
  rw [maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i]
  exact weighted_solutionModeCoeff_le (I := I) (M := M) (a := a) hT.le f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_Ha2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_Ha2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_Ha2_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_Ha2_le

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_norm_deriv_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityDerivField (I := I) (M := M) a hT.le f‖ ≤
      2 * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M) (b := a)
    h_compact (C := 2) (by norm_num) _ f (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i]
  exact weighted_derivModeCoeff_le (I := I) (M := M) (a := a) hT.le f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_deriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_deriv_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_deriv_le

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityOp (I := I) (M := M) a hT f‖ ≤ 2 * ‖f‖ := by
  have hnormsq := TimeSobolev.timeH1.norm_sq_eq
    (maximalRegularityOp (I := I) (M := M) a hT f)
  have hinit : (maximalRegularityOp (I := I) (M := M) a hT f).initial = 0 :=
    rfl
  have hderiv : (maximalRegularityOp (I := I) (M := M) a hT f).deriv =
      maximalRegularityDerivField (I := I) (M := M) a hT.le f := rfl
  have hderiv_le := maximalRegularityOp_norm_deriv_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT f
  have hsq : ‖maximalRegularityOp (I := I) (M := M) a hT f‖ ^ 2 ≤
      (2 * ‖f‖) ^ 2 := by
    rw [hnormsq, hinit, hderiv, norm_zero]
    have h2f_nonneg : 0 ≤ 2 * ‖f‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    nlinarith [hderiv_le, norm_nonneg
      (maximalRegularityDerivField (I := I) (M := M) a hT.le f)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (by norm_num) (norm_nonneg _))] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_norm_le

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
