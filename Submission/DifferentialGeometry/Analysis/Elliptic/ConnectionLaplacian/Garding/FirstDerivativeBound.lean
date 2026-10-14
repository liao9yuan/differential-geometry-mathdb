import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTwoTensor.Basic
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


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma tensorL2Norm_sq_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
  rw [tensorL2Norm_def]
  exact Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_toFun ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_toFun


lemma tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun
        (covGrad (I := I) (M := M) g 0 2 T).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun T.toFun :=
  green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed (I := I) (M := M) g T T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner


theorem covGrad_l2NormSq_le_rawConnLap_mul_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
        tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
  set ΔT : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 T with hΔT_def
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T)]
    rw [hΔT_def]
    exact tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner (I := I) (M := M) g T
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 2 ΔT.toFun T.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔT)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔT T)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_l2NormSq_le_rawConnLap_mul_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_l2NormSq_le_rawConnLap_mul_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_l2NormSq_le_rawConnLap_mul_self ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_l2NormSq_le_rawConnLap_mul_self


theorem covGrad_l2Norm_le_geomMean
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun ≤
      Real.sqrt
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
          tensorL2Norm (I := I) (M := M) g 0 2 T.toFun) := by
  have hsq := covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have hnn : 0 ≤ tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T).toFun :=
    tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1) _
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_l2Norm_le_geomMean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_l2Norm_le_geomMean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_l2Norm_le_geomMean ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_l2Norm_le_geomMean

end Elliptic
end Analysis
end DifferentialGeometry

end
