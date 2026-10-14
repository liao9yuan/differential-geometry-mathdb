import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator.Basic

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

variable {τ : ℝ}

omit [NeZero (Module.finrank ℝ E)] in
private theorem lambda_sq_le (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
  have hlam := tensor_lambda_nonneg (I := I) (M := M) i
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.lambda_sq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.lambda_sq_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem scaleLaplacianWeightMulTwo
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight,
    ← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) 2,
    ← Real.rpow_add hbase_pos]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianWeightMulTwo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianWeightMulTwo target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem weightLambdaMulSqLe
    (v : TensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) * (v.coeff i) ^ 2 := by
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i τ
  have hsq : (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2 ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 * (v.coeff i) ^ 2 := by
    have h := lambda_sq_le (I := I) (M := M) i
    nlinarith [sq_nonneg (v.coeff i), h]
  calc tensorSobolevWeight (I := I) (M := M) i τ *
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i τ *
          ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 *
            (v.coeff i) ^ 2) := mul_le_mul_of_nonneg_left hsq hw_nonneg
    _ = tensorSobolevWeight (I := I) (M := M) i (τ + 2) * (v.coeff i) ^ 2 := by
        rw [← mul_assoc, scaleLaplacianWeightMulTwo (I := I) (M := M) i]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weightLambdaMulSqLe
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.weightLambdaMulSqLe target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem scaleLaplacianWeightedSummable
    (v : TensorHs (I := I) (M := M) g r s (τ + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i τ *
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) v.weighted_summable
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i τ)
      (sq_nonneg _)
  · exact weightLambdaMulSqLe (I := I) (M := M) v i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianWeightedSummable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianWeightedSummable target :: scope.openDecls } }

def scaleLaplacianFun (v : TensorHs (I := I) (M := M) g r s (τ + 2)) :
    TensorHs (I := I) (M := M) g r s τ where
  coeff i := -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i
  weighted_summable := scaleLaplacianWeightedSummable (I := I) (M := M) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scaleLaplacianFun_coeff
    (v : TensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (scaleLaplacianFun (I := I) (M := M) v).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem scaleLaplacianFun_add
    (v w : TensorHs (I := I) (M := M) g r s (τ + 2)) :
    scaleLaplacianFun (I := I) (M := M) (v + w) =
      scaleLaplacianFun (I := I) (M := M) v + scaleLaplacianFun (I := I) (M := M) w := by
  refine TensorHs.ext (funext (fun i => ?_))
  simp only [scaleLaplacianFun_coeff, TensorHs.add_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_add ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_add

omit [NeZero (Module.finrank ℝ E)] in
theorem scaleLaplacianFun_smul (c : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (τ + 2)) :
    scaleLaplacianFun (I := I) (M := M) (c • v) =
      c • scaleLaplacianFun (I := I) (M := M) v := by
  refine TensorHs.ext (funext (fun i => ?_))
  simp only [scaleLaplacianFun_coeff, TensorHs.smul_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.scaleLaplacianFun_smul

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_scaleLaplacianFun_le
    (v : TensorHs (I := I) (M := M) g r s (τ + 2)) :
    ‖scaleLaplacianFun (I := I) (M := M) v‖ ≤ ‖v‖ := by
  have hsq : ‖scaleLaplacianFun (I := I) (M := M) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [TensorHs.norm_sq_eq_tsum (I := I) (M := M),
      TensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((scaleLaplacianFun (I := I) (M := M) v).weighted_summable)
      v.weighted_summable
    rw [scaleLaplacianFun_coeff]
    exact weightLambdaMulSqLe (I := I) (M := M) v i
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_scaleLaplacianFun_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_scaleLaplacianFun_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_scaleLaplacianFun_le ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_scaleLaplacianFun_le

def tensorScaleLaplacian (τ : ℝ) :
    TensorHs (I := I) (M := M) g r s (τ + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g r s τ :=
  LinearMap.mkContinuous
    { toFun := scaleLaplacianFun (I := I) (M := M)
      map_add' := scaleLaplacianFun_add (I := I) (M := M)
      map_smul' := fun c v => scaleLaplacianFun_smul (I := I) (M := M) c v }
    1
    (fun v => by
      change ‖scaleLaplacianFun (I := I) (M := M) v‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact norm_scaleLaplacianFun_le (I := I) (M := M) v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorScaleLaplacian_apply (τ : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (τ + 2)) :
    tensorScaleLaplacian (I := I) (M := M) τ v =
      scaleLaplacianFun (I := I) (M := M) v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_apply

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorScaleLaplacian_coeff (τ : ℝ)
    (v : TensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorScaleLaplacian (I := I) (M := M) τ v).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian_coeff

variable {τ : ℝ} {T : ℝ}

def timeScaleLaplacian (τ : ℝ) {T : ℝ} :
    timeL2 (TensorHs (I := I) (M := M) g r s (τ + 2)) T →L[ℝ]
      timeL2 (TensorHs (I := I) (M := M) g r s τ) T :=
  (tensorScaleLaplacian (I := I) (M := M) τ).compLpL 2 (timeMeasure T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian

omit [NeZero (Module.finrank ℝ E)] in
theorem timeScaleLaplacian_coeFn
    (v : timeL2 (TensorHs (I := I) (M := M) g r s (τ + 2)) T) :
    timeScaleLaplacian (I := I) (M := M) τ v =ᵐ[timeMeasure T]
      fun t => tensorScaleLaplacian (I := I) (M := M) τ (v t) :=
  (tensorScaleLaplacian (I := I) (M := M) τ).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeScaleLaplacian_coeFn

omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_timeScaleLaplacian
    (v : timeL2 (TensorHs (I := I) (M := M) g r s (τ + 2)) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (timeScaleLaplacian (I := I) (M := M) τ v) i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
        timeModeCoeff (I := I) (M := M) v i := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (timeScaleLaplacian (I := I) (M := M) τ v) i
  have hΔ := timeScaleLaplacian_coeFn (I := I) (M := M)
    (τ := τ) v
  have hsmul := Lp.coeFn_smul (-(TensorEigenIdx.lambda (I := I) (M := M) i))
    (timeModeCoeff (I := I) (M := M) v i)
  have hvcoe := timeModeCoeff_coeFn (I := I) (M := M) v i
  filter_upwards [hlhs, hΔ, hsmul, hvcoe] with t ht hΔt hsmt hvt
  rw [ht, hΔt, tensorScaleLaplacian_coeff, hsmt, Pi.smul_apply, hvt, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_timeScaleLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_timeScaleLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_timeScaleLaplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_timeScaleLaplacian

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_solves_perMode {a : ℝ} (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularityDerivField (I := I) (M := M) a hT f) i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
          timeModeCoeff (I := I) (M := M)
            (maximalRegularitySolutionField (I := I) (M := M) a hT f) i +
        timeModeCoeff (I := I) (M := M) f i := by
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i]
  rw [derivModeCoeff, perModeConvolutionDerivL2_apply, solutionModeCoeff, neg_smul,
    ← sub_eq_neg_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves_perMode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves_perMode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves_perMode ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves_perMode

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityOp_solves {a : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT f) =
      timeScaleLaplacian (I := I) (M := M) a
          (maximalRegularitySolutionField (I := I) (M := M) a hT.le f) +
        f := by
  rw [maximalRegularityOp_timeDeriv (I := I) (M := M)
    (a := a) hT f]
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_timeScaleLaplacian (I := I) (M := M) (τ := a)
      (maximalRegularitySolutionField (I := I) (M := M) a hT.le f) i]
  exact maximalRegularityOp_solves_perMode (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.maximalRegularityOp_solves

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
