import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.MetricPerturbation.InverseH2
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.FractionalPower
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.IteratedCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.metricH2 target :: scope.openDecls } }

private abbrev rank2H4 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank2H4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank2H4 target :: scope.openDecls } }

private abbrev rank2H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank2H2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank2H2 target :: scope.openDecls } }

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4H2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rank4H2 target :: scope.openDecls } }

noncomputable def secondCovariantDerivativeH4ToH2
    (g : SmoothRiemannianMetric I M) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank4H2 (I := I) (M := M) g := by
  let J : rank2H4 (I := I) (M := M) g →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + (2 : ℝ)) :=
    (TensorHs.castEquiv (I := I) (M := M)
      (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  exact (iterCovGradHs (I := I) (M := M) g 2 2 2).comp J

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2

noncomputable def cometricDoubleTraceH2
    (g : SmoothRiemannianMetric I M) :
    rank4H2 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 2 2
    (cometricDoubleTraceField (I := I) g 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2

theorem secondCovariantDerivativeH4ToH2_apply_ccTensorToHs
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 2) :
    secondCovariantDerivativeH4ToH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  have hcast :
      (ContinuousLinearEquiv.toContinuousLinearMap
        (TensorHs.castEquiv (I := I) (M := M)
          (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))).toContinuousLinearEquiv)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2
          ((2 : ℝ) + (2 : ℝ)) U := by
    change
      TensorHs.castEquiv (I := I) (M := M)
          (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2
          ((2 : ℝ) + (2 : ℝ)) U
    ext i
    simp only [TensorHs.castEquiv_coeff, ccTensorToHs_coeff]
  rw [secondCovariantDerivativeH4ToH2, ContinuousLinearMap.comp_apply, hcast]
  exact iterCovGradHs_apply_ccTensorToHs (I := I) (M := M) g 2 2 2 U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2_apply_ccTensorToHs ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.secondCovariantDerivativeH4ToH2_apply_ccTensorToHs

theorem cometricDoubleTraceH2_apply_ccTensorToHs
    (g : SmoothRiemannianMetric I M) (V : SmoothCcTensor g 0 4) :
    cometricDoubleTraceH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) V) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceField (I := I) g 2) V) := by
  exact appHs_apply_ccTensorToHs (I := I) (M := M) g 4 2 2
    (cometricDoubleTraceField (I := I) g 2) V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2_apply_ccTensorToHs ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cometricDoubleTraceH2_apply_ccTensorToHs

noncomputable def lowRegularityPrincipalOperatorH2
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g :=
  (cometricDoubleTraceH2 (I := I) (M := M) g).comp
    ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).comp
      (secondCovariantDerivativeH4ToH2 (I := I) (M := M) g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2

theorem lowRegularityPrincipalOperatorH2_norm_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    exists_inverseMetricPerturbationCorrectionH2_norm_bound (I := I) (M := M) hDim g
  let A := cometricDoubleTraceH2 (I := I) (M := M) g
  let D := secondCovariantDerivativeH4ToH2 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT
  have hInv := (hinv T hT).2
  calc
    ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T‖ ≤
        ‖A‖ *
          ‖(inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).comp D‖ := by
      simpa only [lowRegularityPrincipalOperatorH2, A, D] using
        (A.opNorm_comp_le
          ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).comp D))
    _ ≤ ‖A‖ *
          (‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T‖ := by
      dsimp only [C]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_norm_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_norm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_norm_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_norm_bound

theorem lowRegularityPrincipalOperatorH2_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T U : metricH2 (I := I) (M := M) g,
        ‖T‖ ≤ ρ → ‖U‖ ≤ ρ →
          ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T -
              lowRegularityPrincipalOperatorH2 (I := I) (M := M) g U‖ ≤
            C * ‖T - U‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    exists_inverseMetricPerturbationCorrectionH2_lipschitz_bound (I := I) (M := M) hDim g
  let A := cometricDoubleTraceH2 (I := I) (M := M) g
  let D := secondCovariantDerivativeH4ToH2 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U hT hU
  have hInv := hinv T U hT hU
  have hdiff :
      lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T -
          lowRegularityPrincipalOperatorH2 (I := I) (M := M) g U =
        A.comp
          ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
            inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U).comp D) := by
    apply ContinuousLinearMap.ext
    intro V
    simp only [lowRegularityPrincipalOperatorH2, A, D, sub_apply,
      ContinuousLinearMap.comp_apply]
    rw [map_sub]
  rw [hdiff]
  calc
    _ ≤ ‖A‖ *
          ‖(inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
            inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U).comp D‖ :=
      A.opNorm_comp_le _
    _ ≤ ‖A‖ *
          (‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
              inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
          inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T - U‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T - U‖ := by
      dsimp only [C]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_lipschitz_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_lipschitz_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_lipschitz_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegularityPrincipalOperatorH2_lipschitz_bound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
