import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.AllOrder
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Equivalence.SecondOrderSpectralIterate

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

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def ccSpectralEmbed (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    TensorHs (I := I) (M := M) g 0 2 σ where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g σ T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed ``Submission.DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed

@[simp] theorem ccSpectralEmbed_coeff (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (ccSpectralEmbed (I := I) (M := M) g σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 T) i :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_coeff ``Submission.DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_coeff

theorem ccSpectralEmbed_norm_sq_eq_tsum (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g σ T‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 T) i) ^ 2 := by
  rw [TensorHs.norm_sq_eq_tsum (I := I) (M := M)
    (ccSpectralEmbed (I := I) (M := M) g σ T)]
  exact tsum_congr (fun i => by rw [ccSpectralEmbed_coeff])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_sq_eq_tsum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_sq_eq_tsum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_sq_eq_tsum ``Submission.DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_sq_eq_tsum

theorem ccSpectralEmbed_norm_mono (g : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (T : SmoothCcTensor g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g σ T‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g τ T‖ := by
  have hnn_τ : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g τ T‖ := norm_nonneg _
  have hsq : ‖ccSpectralEmbed (I := I) (M := M) g σ T‖ ^ 2 ≤
      ‖ccSpectralEmbed (I := I) (M := M) g τ T‖ ^ 2 := by
    rw [ccSpectralEmbed_norm_sq_eq_tsum, ccSpectralEmbed_norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro i
      have hbase : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        one_le_one_add_lambda (I := I) (M := M) i
      have hw : tensorSobolevWeight (I := I) (M := M) i σ ≤
          tensorSobolevWeight (I := I) (M := M) i τ := by
        unfold tensorSobolevWeight
        exact Real.rpow_le_rpow_of_exponent_le hbase hστ
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    · exact (ccSpectralEmbed (I := I) (M := M) g σ T).weighted_summable
    · exact (ccSpectralEmbed (I := I) (M := M) g τ T).weighted_summable
  exact le_of_sq_le_sq hsq hnn_τ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_mono ``Submission.DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_norm_mono

theorem ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g ((2 * k : ℕ) : ℝ) T‖ ^ 2 =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)‖ ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2
    with hcompact_def
  rw [ccSpectralEmbed_norm_sq_eq_tsum]
  have h_term :
      (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
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
  exact tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2 ``Submission.DifferentialGeometry.Analysis.Spectral.ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2

theorem tensorL2Coeff_ofCompact_rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g
      0 2))
    (T : SmoothCcTensor g 0 2) (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i := by
  have hraw_eq : rawTensorConnLapSmooth (I := I) g 0 2 T =
      T - oneMinusConnLapSmooth (I := I) g 0 2 T := by
    rw [show oneMinusConnLapSmooth (I := I) g 0 2 T =
        T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl]
    abel
  rw [hraw_eq, map_sub, sub_eq_add_neg,
    show (- SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T)) =
      (-1 : ℝ) • SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T) by
      rw [neg_one_smul],
    tensorL2Coeff_add, tensorL2Coeff_smul,
    tensorL2Coeff_ofCompact_oneMinusConnLapSmooth (I := I) (M := M) g h_compact T i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapSmooth ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapSmooth

theorem tensorL2Coeff_ofCompact_rawTensorConnLapIter
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g
      0 2))
    (T : SmoothCcTensor g 0 2) (i : TensorEigenIdx (I := I) (M := M) g 0 2) (j : ℕ) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rawTensorConnLapIter_succ,
        tensorL2Coeff_ofCompact_rawTensorConnLapSmooth
          (I := I) (M := M) g h_compact (rawTensorConnLapIter (I := I) g 0 2 j T) i,
        ih, pow_succ]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapIter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapIter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapIter ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_rawTensorConnLapIter

theorem rawConnLapIter_l2_le_ccSpectralEmbed_even
    (g : SmoothRiemannianMetric I M) (j : ℕ) (T : SmoothCcTensor g 0 2) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2
    with hcompact_def
  have hnn : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ :=
    norm_nonneg _
  have hsq :
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ^ 2 ≤
        ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ ^ 2 := by
    rw [ccSpectralEmbed_norm_sq_eq_tsum,
      ← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T))]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro i
      rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g h_compact T i j]
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i with hc_def
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) i ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) i := by linarith
      have hlhs_eq : ((- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j * c) ^ 2 =
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * c ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm j 2,
          (even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]
      rw [hlhs_eq]
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) i ((2 * j : ℕ) : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      have hpow_le : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) :=
        pow_le_pow_left₀ hbase_nn hbase_le (2 * j)
      exact mul_le_mul_of_nonneg_right hpow_le (sq_nonneg c)
    · exact tensorL2Coeff_summable_sq (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T))
    · exact (ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T).weighted_summable
  exact le_of_sq_le_sq hsq hnn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.rawConnLapIter_l2_le_ccSpectralEmbed_even then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.rawConnLapIter_l2_le_ccSpectralEmbed_even"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.rawConnLapIter_l2_le_ccSpectralEmbed_even ``Submission.DifferentialGeometry.Analysis.Spectral.rawConnLapIter_l2_le_ccSpectralEmbed_even

theorem tensorPouSobolevHsNorm_le_ccSpectralEmbed (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * ‖ccSpectralEmbed (I := I) (M := M) g ((2 * k : ℕ) : ℝ) T‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hGarding⟩ :=
    DifferentialGeometry.Analysis.Elliptic.exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
      (I := I) (M := M) g 2 k
  refine ⟨Cg * (k + 1), by positivity, fun T => ?_⟩
  set Nspec : ℝ := ‖ccSpectralEmbed (I := I) (M := M) g ((2 * k : ℕ) : ℝ) T‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hterm : ∀ j ∈ Finset.range (k + 1),
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤ Nspec := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ :=
      rawConnLapIter_l2_le_ccSpectralEmbed_even (I := I) (M := M) g j T
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g ((2 * j : ℕ) : ℝ) T‖ ≤ Nspec := by
      rw [hNspec_def]
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g ?_ T
      have : (2 * j : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  have hsum_le :
      ∑ j ∈ Finset.range (k + 1),
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
      (k + 1 : ℝ) * Nspec := by
    calc ∑ j ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖
        ≤ ∑ _j ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hterm
      _ = (k + 1 : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
      ≤ Cg * ∑ j ∈ Finset.range (k + 1),
          ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := hGarding T
    _ ≤ Cg * ((k + 1 : ℝ) * Nspec) := mul_le_mul_of_nonneg_left hsum_le hCg_nn
    _ = (Cg * (k + 1)) * Nspec := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorPouSobolevHsNorm_le_ccSpectralEmbed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorPouSobolevHsNorm_le_ccSpectralEmbed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorPouSobolevHsNorm_le_ccSpectralEmbed ``Submission.DifferentialGeometry.Analysis.Spectral.tensorPouSobolevHsNorm_le_ccSpectralEmbed

end Spectral
end Analysis
end DifferentialGeometry

end
