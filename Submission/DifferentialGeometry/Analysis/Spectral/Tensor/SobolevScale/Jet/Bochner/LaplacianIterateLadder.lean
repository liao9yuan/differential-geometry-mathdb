import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalTerm.EnergyPairing
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.SobolevScaleSummability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ladder_weight_natCast (g₀ : SmoothRiemannianMetric I M)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) (n : ℕ) :
    tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
  unfold tensorSobolevWeight
  rw [Real.rpow_natCast]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.ladder_weight_natCast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.ladder_weight_natCast target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tensorL2Inner_self_eq_norm_toL2_sq (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (X : SmoothCcTensor g₀ r s) :
    tensorL2Inner (I := I) (M := M) g₀ r s X.toFun X.toFun =
      ‖SmoothCcTensor.toL2 X‖ ^ 2 := by
  have h1 : (⟪SmoothCcTensor.toL2 X, SmoothCcTensor.toL2 X⟫_ℝ : ℝ) =
      tensorL2Inner (I := I) (M := M) g₀ r s X.toFun X.toFun := by
    rw [SmoothCcTensor.inner_toL2]
    exact SmoothCcTensor.inner_def X X
  rw [← h1, real_inner_self_eq_norm_sq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Inner_self_eq_norm_toL2_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.tensorL2Inner_self_eq_norm_toL2_sq target :: scope.openDecls } }

theorem smoothCcToTensorHs_even_norm_eq_toL2_iter (g₀ : SmoothRiemannianMetric I M)
    (p : ℕ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ := by
  classical
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ ^ 2 =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ ^ 2 := by
    rw [TensorHs.norm_sq_eq_tsum,
      ← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))]
    refine tsum_congr (fun i => ?_)
    rw [smoothCcToTensorHs_coeff,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) w i p,
      ladder_weight_natCast (I := I) (M := M) g₀ i (2 * p)]
    ring
  have h1 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ :=
    norm_nonneg _
  have h2 : 0 ≤ ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ :=
    norm_nonneg _
  nlinarith [hsq, h1, h2,
    sq_nonneg (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ -
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_even_norm_eq_toL2_iter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_even_norm_eq_toL2_iter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_even_norm_eq_toL2_iter ``Submission.DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_even_norm_eq_toL2_iter

theorem smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) w‖ ^ 2 =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ ^ 2 +
        ‖SmoothCcTensor.toL2 (covGrad (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))‖ ^ 2 := by
  classical
  have hterm : ∀ i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i ((2 * p + 1 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) w).coeff i) ^ 2 =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)) i := by
    intro i
    rw [smoothCcToTensorHs_coeff,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmooth (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w) i,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) w i p,
      ladder_weight_natCast (I := I) (M := M) g₀ i (2 * p + 1)]
    ring
  have hcross := tensorL2Inner_eq_tsum_l2Coeff_cross
    (I := I) (M := M) (g₀ := g₀)
    (A := oneMinusConnLapSmooth (I := I) g₀ 0 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))
    (B := oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)
  have hadd := oneMinusConnLapSmooth_l2Inner_eq_add_covGrad (I := I) (M := M) g₀ 0 2
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)
  have heq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) w‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmooth (I := I) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)).toFun
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w).toFun := by
    rw [TensorHs.norm_sq_eq_tsum, hcross]
    exact tsum_congr hterm
  rw [heq, hadd,
    tensorL2Inner_self_eq_norm_toL2_sq (I := I) (M := M) g₀ 0 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w),
    tensorL2Inner_self_eq_norm_toL2_sq (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad ``Submission.DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad

theorem smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
    (g₀ : SmoothRiemannianMetric I M) (j : ℕ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖ := by
  classical
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ ^ 2 =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖ ^ 2 := by
    rw [TensorHs.norm_sq_eq_tsum, TensorHs.norm_sq_eq_tsum]
    refine tsum_congr (fun i => ?_)
    rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmooth (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) w i,
      ladder_weight_natCast (I := I) (M := M) g₀ i (j + 2),
      ladder_weight_natCast (I := I) (M := M) g₀ i j]
    ring
  have h1 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ :=
    norm_nonneg _
  have h2 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
      (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖ := norm_nonneg _
  nlinarith [hsq, h1, h2,
    sq_nonneg (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ -
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
        (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap ``Submission.DifferentialGeometry.Analysis.Spectral.smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap

end Spectral
end Analysis
end DifferentialGeometry

end
