import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.Smoothing
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode.Endpoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.intervalIntegral
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

section Scalar

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

abbrev duhamelKernelSqIntegral :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.duhamelKernelSqIntegral

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral ``Submission.DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral

theorem two_lambda_mul_duhamelKernelSqIntegral (lam t : ℝ) :
    (2 * lam) * duhamelKernelSqIntegral lam t = 1 - Real.exp (-(2 * lam * t)) :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.two_lambda_mul_duhamelKernelSqIntegral
    lam t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.two_lambda_mul_duhamelKernelSqIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.two_lambda_mul_duhamelKernelSqIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.two_lambda_mul_duhamelKernelSqIntegral ``Submission.DifferentialGeometry.Analysis.Spectral.two_lambda_mul_duhamelKernelSqIntegral

theorem duhamelKernelSqIntegral_nonneg {lam t : ℝ} (ht : 0 ≤ t) :
    0 ≤ duhamelKernelSqIntegral lam t :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.duhamelKernelSqIntegral_nonneg ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_nonneg

theorem duhamelKernelSqIntegral_le_t {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    duhamelKernelSqIntegral lam t ≤ t :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.duhamelKernelSqIntegral_le_t hlam ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_le_t then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_le_t"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_le_t ``Submission.DifferentialGeometry.Analysis.Spectral.duhamelKernelSqIntegral_le_t

theorem one_add_lambda_mul_duhamel_kernel_sq_integral_le {lam t : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (1 + lam) * duhamelKernelSqIntegral lam t ≤ t + 1 / 2 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_duhamel_kernel_sq_integral_le
    hlam ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_duhamel_kernel_sq_integral_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_duhamel_kernel_sq_integral_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_duhamel_kernel_sq_integral_le ``Submission.DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_duhamel_kernel_sq_integral_le

variable {f : ℝ → ℝ}

theorem perModeConvolution_endpoint_sq_le (lam : ℝ) (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) :
    (perModeConvolution lam f t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.perModeConvolution_endpoint_sq_le lam hf ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.perModeConvolution_endpoint_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.perModeConvolution_endpoint_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.perModeConvolution_endpoint_sq_le ``Submission.DifferentialGeometry.Analysis.Spectral.perModeConvolution_endpoint_sq_le

theorem one_add_lambda_mul_perModeConvolution_endpoint_sq_le (lam : ℝ)
    (hlam : 0 ≤ lam) (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (1 + lam) * (perModeConvolution lam f t) ^ 2
      ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_perModeConvolution_endpoint_sq_le
    lam hlam hf ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_perModeConvolution_endpoint_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_perModeConvolution_endpoint_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_perModeConvolution_endpoint_sq_le ``Submission.DifferentialGeometry.Analysis.Spectral.one_add_lambda_mul_perModeConvolution_endpoint_sq_le

end Scalar

section

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

omit [NeZero (Module.finrank ℝ E)] in
theorem duhamel_endpoint_value_weighted_summable
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (c + 1) *
        (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hmass.mul_left (t + 1 / 2))
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (c + 1))
      (sq_nonneg _)
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hweight_split :
        tensorSobolevWeight (I := I) (M := M) i (c + 1) =
          tensorSobolevWeight (I := I) (M := M) i c * (1 + lam) := by
      have hbase_pos : (0 : ℝ) < 1 + lam :=
        lt_of_lt_of_le one_pos (by linarith)
      rw [tensorSobolevWeight, tensorSobolevWeight, hlam_def, Real.rpow_add hbase_pos,
        Real.rpow_one]
    have hwc_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i c
    have hgain := one_add_lambda_mul_perModeConvolution_endpoint_sq_le
      (f := φ i) lam hlam_nn (hφ i) ht
    calc tensorSobolevWeight (I := I) (M := M) i (c + 1) *
            (perModeConvolution lam (φ i) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i c *
            ((1 + lam) * (perModeConvolution lam (φ i) t) ^ 2) := by
          rw [hweight_split]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i c *
            ((t + 1 / 2) * ∫ s in (0 : ℝ)..t, (φ i s) ^ 2) :=
          mul_le_mul_of_nonneg_left hgain hwc_nn
      _ = (t + 1 / 2) * (tensorSobolevWeight (I := I) (M := M) i c *
            ∫ s in (0 : ℝ)..t, (φ i s) ^ 2) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_weighted_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_weighted_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_weighted_summable ``Submission.DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_weighted_summable

def duhamelValueHs {g : SmoothRiemannianMetric I M} {r s : ℕ} (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    TensorHs (I := I) (M := M) g r s (c + 1) where
  coeff i := perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t
  weighted_summable :=
    duhamel_endpoint_value_weighted_summable (I := I) (M := M) c ht φ hφ hmass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamelValueHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamelValueHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamelValueHs ``Submission.DifferentialGeometry.Analysis.Spectral.duhamelValueHs

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem duhamelValueHs_coeff {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (duhamelValueHs (I := I) (M := M) c ht φ hφ hmass).coeff i =
      perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamelValueHs_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamelValueHs_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamelValueHs_coeff ``Submission.DifferentialGeometry.Analysis.Spectral.duhamelValueHs_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem duhamel_endpoint_value_summable_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {c : ℝ} (hc : 0 ≤ c) {t : ℝ}
    (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) :=
  TensorHs.coeff_summable_sq_of_nonneg (I := I) (M := M) (by linarith : 0 ≤ c + 1)
    (duhamelValueHs (I := I) (M := M) c ht φ hφ hmass)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_summable_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_summable_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_summable_sq ``Submission.DifferentialGeometry.Analysis.Spectral.duhamel_endpoint_value_summable_sq

omit [NeZero (Module.finrank ℝ E)] in
theorem duhamel_into_all_tensorHs {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {t : ℝ} (ht : 0 ≤ t)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hsmooth : ∀ c : ℝ, 0 ≤ c →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    ∃ u : TensorL2 r s g,
      (∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i =
        perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ∧
      ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : TensorHs (I := I) (M := M) g r s σ,
          tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
              h_compact hσ v = u := by
  classical
  set bsis := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hbsis_def
  have hval_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) :=
    duhamel_endpoint_value_summable_sq (I := I) (M := M) (c := 0) le_rfl ht φ hφ
      (hsmooth 0 le_rfl)
  have hmemℓp : Memℓp (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t‖ ^
            (2 : ℝ≥0∞).toReal) =
        (fun i => (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
          (φ i) t) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [h_eq]; exact hval_summable
  set u : TensorL2 r s g := bsis.repr.symm ⟨_, hmemℓp⟩ with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i =
      perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := by
    intro i
    rw [tensorL2Coeff, hu_def, hbsis_def,
      LinearIsometryEquiv.apply_symm_apply]
  refine ⟨u, hu_coeff, fun σ hσ => ?_⟩
  set c : ℝ := _root_.Max.max (σ - 1) 0 with hc_def
  have hc_nn : 0 ≤ c := le_max_right _ _
  have hσ_le : σ ≤ c + 1 := by
    have : σ - 1 ≤ c := le_max_left _ _; linarith
  set vTop : TensorHs (I := I) (M := M) g r s (c + 1) :=
    duhamelValueHs (I := I) (M := M) (c := c) ht φ hφ (hsmooth c hc_nn) with hvTop_def
  have hv_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i σ * (vTop.coeff i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) vTop.weighted_summable
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
        (sq_nonneg _)
    · have hbase : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        one_le_one_add_lambda (I := I) (M := M) i
      have hwle : tensorSobolevWeight (I := I) (M := M) i σ ≤
          tensorSobolevWeight (I := I) (M := M) i (c + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase hσ_le
      exact mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
  set v : TensorHs (I := I) (M := M) g r s σ :=
    { coeff := vTop.coeff, weighted_summable := hv_summable } with hv_def
  refine ⟨v, ?_⟩
  refine bsis.repr.injective ?_
  ext i
  have hcoeff_lhs : (bsis.repr (tensorHsToL2 (I := I) (M := M)
        (g := g) (r := r) (s := s) h_compact hσ v)) i =
      tensorL2Coeff (I := I) (M := M) h_compact
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ v) i := rfl
  have hcoeff_rhs : (bsis.repr u) i =
      tensorL2Coeff (I := I) (M := M) h_compact u i := rfl
  rw [hcoeff_lhs, hcoeff_rhs,
    tensorHsToL2_tensorL2Coeff
      (I := I) (M := M) (h_compact := h_compact) hσ v i,
    hu_coeff i]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.duhamel_into_all_tensorHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.duhamel_into_all_tensorHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.duhamel_into_all_tensorHs ``Submission.DifferentialGeometry.Analysis.Spectral.duhamel_into_all_tensorHs

theorem exists_smooth_tensor_representative_of_duhamel_smoothing
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (h_gate : SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hsmooth : ∀ c : ℝ, 0 ≤ c →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i c *
          ∫ q in (0 : ℝ)..t, (φ i q) ^ 2)) :
    ∃ T : SmoothCcTensor g r s,
      ∀ i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (T : TensorL2 r s g) i =
        perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := by
  obtain ⟨u, hu_coeff, hu_all⟩ :=
    duhamel_into_all_tensorHs (I := I) (M := M) ht
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
      φ hφ hsmooth
  obtain ⟨T, hT⟩ := h_gate u hu_all
  refine ⟨T, fun i => ?_⟩
  rw [hT]
  exact hu_coeff i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_smooth_tensor_representative_of_duhamel_smoothing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_smooth_tensor_representative_of_duhamel_smoothing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_smooth_tensor_representative_of_duhamel_smoothing ``Submission.DifferentialGeometry.Analysis.Spectral.exists_smooth_tensor_representative_of_duhamel_smoothing

end

end Spectral
end Analysis
end DifferentialGeometry

end
