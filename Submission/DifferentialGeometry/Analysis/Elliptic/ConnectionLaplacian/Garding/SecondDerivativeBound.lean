import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Basic
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
  [Module.Finite ℝ E]
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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }


lemma covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 2 T₀)
    (covGrad (I := I) (M := M) g 0 2 T₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner


theorem secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun *
        tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun := by
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T₀ with hS_def
  set ΔS : SmoothCcTensor g 0 3 := rawTensorConnLapSmooth (I := I) g 0 3 S
    with hΔS_def
  change tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 3 ΔS.toFun *
        tensorL2Norm (I := I) (M := M) g 0 3 S.toFun
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (3 + 1)
      (covGrad (I := I) (M := M) g 0 3 S)]
    rw [hΔS_def, hS_def]
    exact covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner (I := I) (M := M) g T₀
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 3 ΔS.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔS)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔS S)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad ``Submission.DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad


theorem covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toFun
        (covGrad (I := I) (M := M) g 0 2 T₀).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 := by
  set ΔT₀ : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 T₀
    with hΔT₀_def
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 (2 + 1)
    (covGrad (I := I) (M := M) g 0 2 ΔT₀).toFun
    (covGrad (I := I) (M := M) g 0 2 T₀).toFun]
  rw [green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed (I := I) (M := M) g T₀ ΔT₀]
  rw [hΔT₀_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T₀)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq

end Elliptic
end Analysis
end DifferentialGeometry

end
