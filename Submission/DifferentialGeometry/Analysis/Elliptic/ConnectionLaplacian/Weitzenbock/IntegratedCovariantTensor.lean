import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Lowering
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.FirstDerivativeBound
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz

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


lemma covGrad_l2Inner_self_eq_neg_rawConnLap_inner_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor (I := I) (M := M) g (s + 1)
    (covGrad (I := I) (M := M) g 0 s S)
    (covGrad (I := I) (M := M) g 0 s S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawConnLap_inner_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawConnLap_inner_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawConnLap_inner_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_l2Inner_self_eq_neg_rawConnLap_inner_covariantTensor


lemma covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 := by
  set ΔS : SmoothCcTensor g 0 s := rawTensorConnLapSmooth (I := I) g 0 s S with hΔS_def
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s ΔS).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_covariantTensor (I := I) (M := M) g s S ΔS]
  rw [hΔS_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_covariantTensor


lemma rawConnLap_l2Inner_covGrad_split_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set GS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hGS_def
  set ΔGS : SmoothCcTensor g 0 (s + 1) :=
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) GS with hΔGS_def
  set GΔ : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_covariantTensor (I := I) (M := M) g s S]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawConnLap_l2Inner_covGrad_split_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawConnLap_l2Inner_covGrad_split_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawConnLap_l2Inner_covGrad_split_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.rawConnLap_l2Inner_covGrad_split_covariantTensor


theorem weitzenbock_integrated_covGrad_l2_normSq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (s + 1 + 1)
    (covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S))]
  rw [covGrad_l2Inner_self_eq_neg_rawConnLap_inner_covariantTensor (I := I) (M := M) g s S]
  rw [rawConnLap_l2Inner_covGrad_split_covariantTensor (I := I) (M := M) g s S]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq ``Submission.DifferentialGeometry.Analysis.Elliptic.weitzenbock_integrated_covGrad_l2_normSq

end Elliptic
end Analysis
end DifferentialGeometry

end
