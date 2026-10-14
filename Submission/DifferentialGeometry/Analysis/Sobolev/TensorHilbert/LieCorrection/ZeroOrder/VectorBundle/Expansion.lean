import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.Coefficient.Decomposition
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.MixedConnectionExpansion
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Integral.Connection

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ =
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  let v : Fin 3 → TangentSpace I x := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)
  have hm : (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) = m := by
    funext i
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  rw [← hm]
  rw [metricLoweredConnectionDifference_unitModel_apply, connectionDifferenceLoweredCc_unitModel_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc ``Submission.DifferentialGeometry.Integral.Connection.metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem operatorFieldComposition_cometricCast_eq_reindexedPureTrace (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 3) :
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) W =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)) W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  simp only [unitModel, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  let Z : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x)
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricCastG0 (I := I) g₀ g₁).toSection x) Z) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x) Z)
  rw [show
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x) Z =
        lieCorrectionZeroTraceStep (I := I) g₁ 1 (Equiv.refl _) x Z from
      congrFun (congrArg DFunLike.coe
        (reindexedPureTrace_toSection (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _) x)) Z]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.operatorFieldComposition_cometricCast_eq_reindexedPureTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.operatorFieldComposition_cometricCast_eq_reindexedPureTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.operatorFieldComposition_cometricCast_eq_reindexedPureTrace ``Submission.DifferentialGeometry.Integral.Connection.operatorFieldComposition_cometricCast_eq_reindexedPureTrace

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (g₀ g₁ : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) := by
  unfold deTurckVectorFieldCovector
  rw [metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc]
  calc
    operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) :=
      (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).symm
    _ = _ := operatorFieldComposition_cometricCast_eq_reindexedPureTrace (I := I) (M := M) g₀ g₁ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp ``Submission.DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (g₀ g₁ gA gB : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA -
        deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
          metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gA) := by
  unfold deTurckVectorFieldCovector
  have hXi :
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA -
        metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB =
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
        metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gA := by
    unfold metricLoweredConnectionDifference
    abel
  calc
    operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA) -
        operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) :=
      congrArg₂ (· - ·)
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1
          (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA)).symm
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1
          (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB)).symm
    _ = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA -
          metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) :=
      (operatorFieldComposition_sub_right (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB)).symm
    _ = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
          metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gA) := congrArg _ hXi
    _ = _ := operatorFieldComposition_cometricCast_eq_reindexedPureTrace (I := I) (M := M) g₀ g₁ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp ``Submission.DifferentialGeometry.Integral.Connection.deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp

noncomputable def lieCorrectionZeroVectorBundleExpansion (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
      (ipLowCc (I := I) (M := M) g₀
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundleExpansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundleExpansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundleExpansion ``Submission.DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundleExpansion

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundle_eq_expansion (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁ =
      lieCorrectionZeroVectorBundleExpansion (I := I) (M := M) g₀ g₁ := by
  rw [lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp, lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundle_eq_expansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundle_eq_expansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundle_eq_expansion ``Submission.DifferentialGeometry.Integral.Connection.lieCorrectionZeroVectorBundle_eq_expansion

end DifferentialGeometry.Integral.Connection
