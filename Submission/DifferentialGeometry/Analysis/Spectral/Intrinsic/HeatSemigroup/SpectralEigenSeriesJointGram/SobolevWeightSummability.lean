import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.MassUniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Regularity.InteriorTimeSmoothing
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.SmoothRepresentativeRealization
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.EigenCombination
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.MetricGramDifference
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RawComponentIdentification
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.OrderDropping
import Submission.DifferentialGeometry.Analysis.Calculus.Smoothness.Tsum
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.WeylSummability
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SobolevDecay
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.Regularity.JointChart
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame
import Submission.DifferentialGeometry.Analysis.Calculus.Smoothness.AnisotropicJoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma weight_two_rpow_eq_sq (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (pp : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (2 * pp)
      = ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pp) ^ 2 := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  unfold tensorSobolevWeight
  rw [show (2 : ℝ) * pp = pp * 2 by ring, Real.rpow_mul hbase_pos.le, Real.rpow_two]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.weight_two_rpow_eq_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.weight_two_rpow_eq_sq target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma abs_le_sqrt_of_weight_sq_le (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (pp : ℝ) {v C : ℝ}
    (h : tensorSobolevWeight (I := I) (M := M) i (2 * pp) * v ^ 2 ≤ C) :
    |v| ≤ Real.sqrt C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-pp) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hw := weight_two_rpow_eq_sq (I := I) (M := M) g i pp
  rw [hw] at h
  set W : ℝ := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pp with hW_def
  have hW_pos : 0 < W := Real.rpow_pos_of_pos hbase_pos _
  have hC_nn : 0 ≤ C := le_trans (by positivity) h
  have habs : |v| ≤ Real.sqrt C / W := by
    rw [le_div_iff₀ hW_pos]
    have h2 : (|v| * W) ^ 2 ≤ (Real.sqrt C) ^ 2 := by
      rw [Real.sq_sqrt hC_nn, mul_pow, sq_abs]
      nlinarith [h, hW_pos.le]
    have hlhs_nn : 0 ≤ |v| * W := by positivity
    nlinarith [Real.sqrt_nonneg C, h2, hlhs_nn,
      sq_nonneg (|v| * W - Real.sqrt C)]
  rw [Real.rpow_neg hbase_pos.le]
  rw [div_eq_mul_inv] at habs
  rwa [← hW_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.abs_le_sqrt_of_weight_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.abs_le_sqrt_of_weight_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.abs_le_sqrt_of_weight_sq_le ``Submission.DifferentialGeometry.Analysis.Spectral.abs_le_sqrt_of_weight_sq_le

omit [BoundarylessManifold I M] in
lemma summable_sqrt_mul_weight_neg (g : SmoothRiemannianMetric I M)
    (Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (hCm : Summable Cm)
    (hCm_nn : ∀ i, 0 ≤ Cm i) {sW : ℝ} (hsW : ((weylSobolevExp (E := E) : ℕ) : ℝ) < sW) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)) := by
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(2 * sW))) := by
    refine tensorEigen_summable_negpow (I := I) (M := M) g (2 * sW) ?_
    have h0 : (0 : ℝ) ≤ ((weylSobolevExp (E := E) : ℕ) : ℝ) := by positivity
    nlinarith [h0]
  have hw_sq : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorSobolevWeight (I := I) (M := M) i (-sW) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-(2 * sW)) := by
    intro i
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-sW)) 2,
      ← Real.rpow_mul (hbase_pos i).le]
    congr 1; push_cast; ring
  have hbound : ∀ i, Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)
      ≤ (Cm i + tensorSobolevWeight (I := I) (M := M) i (-(2 * sW))) / 2 := by
    intro i
    have h1 : Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)
        ≤ (Real.sqrt (Cm i) ^ 2 + tensorSobolevWeight (I := I) (M := M) i (-sW) ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt (Cm i) - tensorSobolevWeight (I := I) (M := M) i (-sW)),
        Real.sq_sqrt (hCm_nn i)]
    rw [Real.sq_sqrt (hCm_nn i), hw_sq i] at h1
    exact h1
  have hnn : ∀ i, 0 ≤ Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW) :=
    fun i => mul_nonneg (Real.sqrt_nonneg _)
      (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  exact Summable.of_nonneg_of_le hnn hbound ((hCm.add hweyl).div_const 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.summable_sqrt_mul_weight_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.summable_sqrt_mul_weight_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.summable_sqrt_mul_weight_neg ``Submission.DifferentialGeometry.Analysis.Spectral.summable_sqrt_mul_weight_neg

end Spectral
end Analysis
end DifferentialGeometry

end
