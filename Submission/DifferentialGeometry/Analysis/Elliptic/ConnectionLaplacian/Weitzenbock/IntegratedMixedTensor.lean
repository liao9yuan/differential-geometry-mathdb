import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Mixed
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Weitzenbock.IntegratedCovariantTensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }


omit [CompactSpace M] in
lemma covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun =
      - tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r (s + 1)
    (loweringIntertwinerRS_holds (I := I) (M := M) g r (s + 1))
    (covGrad (I := I) (M := M) g r s S)
    (covGrad (I := I) (M := M) g r s S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs


omit [CompactSpace M] in
lemma covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      - tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 := by
  set ΔS : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
  rw [tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s ΔS).toFun
    (covGrad (I := I) (M := M) g r s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r s
    (loweringIntertwinerRS_holds (I := I) (M := M) g r s) S ΔS]
  rw [hΔS_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s S)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs


omit [CompactSpace M] in
lemma rawTensorConnLap_l2Inner_covGrad_split_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (rawTensorConnLapSmooth (I := I) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      - tensorL2Norm (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  set GS : SmoothCcTensor g r (s + 1) := covGrad (I := I) (M := M) g r s S with hGS_def
  set ΔGS : SmoothCcTensor g r (s + 1) :=
    rawTensorConnLapSmooth (I := I) g r (s + 1) GS with hΔGS_def
  set GΔ : SmoothCcTensor g r (s + 1) :=
    covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g r (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs (I := I) (M := M) g r s S]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_l2Inner_covGrad_split_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_l2Inner_covGrad_split_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_l2Inner_covGrad_split_rs ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_l2Inner_covGrad_split_rs


omit [CompactSpace M] in
theorem weitzenbock_integrated_covGrad_l2_normSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g r (s + 1 + 1)
    (covGrad (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s S))]
  rw [covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs (I := I) (M := M) g r s S]
  rw [rawTensorConnLap_l2Inner_covGrad_split_rs (I := I) (M := M) g r s S]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq_rs ``Submission.DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq_rs

end Elliptic
end Analysis
end DifferentialGeometry

end
