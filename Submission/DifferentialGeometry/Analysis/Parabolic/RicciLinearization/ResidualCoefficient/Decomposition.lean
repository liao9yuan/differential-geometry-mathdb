import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SecondGradient
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.PointwiseBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.PathLinearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Curvature.DecompositionMonomialBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConnectionDifference.Coefficients
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.InputSlotSymmetrization
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.MetricPerturbation
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.ConnectionCommutator
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.SharpGradientKoszul
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.RicciContraction
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.BackgroundDifference
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.FrameContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma residualMetricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.residualMetricCcTensor_unitModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.residualMetricCcTensor_unitModel_apply target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem residualPerturbation_eq_metricDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    P = metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ := by
  have hsymm : ccTensor02Symm (I := I) (M := M) g₀ P = P :=
    ccTensor02Symm_eq_self (I := I) (M := M) g₀ P hPsymm
  have hmd : metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
      ccTensor02Symm (I := I) (M := M) g₀ P := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [show metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
        metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀
        from rfl]
    rw [unitModel_sub_local (I := I) (M := M) g₀ 2
      (metricCcTensor (I := I) (M := M) g₀ g₁) (metricCcTensor (I := I) (M := M) g₀ g₀) x]
    rw [sub_apply]
    rw [residualMetricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      residualMetricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
    rw [show unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x m =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x ![m 0, m 1]
          from by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x (m 0) (m 1)]
    rw [smoothCcTensorBilinForm_ccTensor02Symm (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rw [htie x (m 0) (m 1)]
    ring
  rw [hmd, hsymm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.residualPerturbation_eq_metricDifference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.residualPerturbation_eq_metricDifference target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem ccTensor22_ext_of_operatorFieldApply (g₀ : SmoothRiemannianMetric I M)
    (C D : SmoothCcTensor g₀ 2 2)
    (h : ∀ W : SmoothCcTensor g₀ 0 2,
      operatorFieldApply (I := I) (M := M) g₀ 2 2 C W = operatorFieldApply (I := I) (M := M) g₀ 2 2
        D W) : C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  set V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u))
    with hV_def
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW₀_def
  have h1 : (operatorFieldApply (I := I) (M := M) g₀ 2 2 C W₀).toSection x =
      (operatorFieldApply (I := I) (M := M) g₀ 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
          (unitTensor (I := I) (M := M) x)) := by
    have h1' := congrArg (fun (T : TensorRSSpace 0 2 I x) =>
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T)
        (unitTensor (I := I) (M := M) x)) h1
    exact h1'
  have hWval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (unitTensor (I := I) (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW, hV_def]
    change ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
          (1 : ℝ)) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hWval] at h2
  exact h2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensor22_ext_of_operatorFieldApply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensor22_ext_of_operatorFieldApply target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    (1 / 2 : ℝ) • (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀) =
      ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₁
        + backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g₀ g₁
        + decompositionKernelContractionField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := residualPerturbation_eq_metricDifference (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine ccTensor22_ext_of_operatorFieldApply (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    ricciOrderZeroRiemannHalfBackgroundDiff_operatorFieldApplication_eq_residualFieldSum_add_decompositionKernelSecondGrad
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [operatorFieldApplication_smul_left (I := I) (M := M) g₀ 2 2, operatorFieldApplication_sub_left (I := I) (M := M) g₀ 2 2]
  rw [hprim]
  rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (ricciOrderZeroBackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
          - ricciOrderZeroBackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          ricciCovariantTermSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
      - ricciContractionRemainderField (I := I) (M := M) g₀ g₁
          (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)) =
      backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g₀ g₁ from rfl]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₁)
    (backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g₀ g₁) W]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₁
      + backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g₀ g₁)
    (decompositionKernelContractionField (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₁)
    (backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g₀ g₁) W]
  rw [operatorFieldApplication_decompositionKernelContractionField (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem linearizedRicciConnectionDifferenceOrder0RiemannHalfBackgroundDiffCombInputSymm_eq_residualFieldSum
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    ccInputSlotSymm (I := I) (M := M) g₀
        (linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • (ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀)) =
      ccInputSlotSymm (I := I) (M := M) g₀
          (ricciOrderZeroAACommCoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (backgroundRicciCommutatorDiffDecompositionRemainderField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (decompositionKernelContractionField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) := by
  rw [halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (I := I) (M := M) g₀ g₁ P htie hPsymm]
  rw [ccInputSlotSymm_add (I := I) (M := M) g₀, ccInputSlotSymm_add (I := I) (M := M) g₀,
    ccInputSlotSymm_add (I := I) (M := M) g₀]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0RiemannHalfBackgroundDiffCombInputSymm_eq_residualFieldSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0RiemannHalfBackgroundDiffCombInputSymm_eq_residualFieldSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0RiemannHalfBackgroundDiffCombInputSymm_eq_residualFieldSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0RiemannHalfBackgroundDiffCombInputSymm_eq_residualFieldSum

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricCcTensor_apply (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x v w =
      g.inner x v w := by
  let _ := Tensor0SBundle.tensor0SBundleTopology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hround : ccTensorMultilinear (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x =
      metricCcTensorFib (I := I) g x := by
    unfold ccTensorMultilinear metricCcTensor
    unfold MixedSection.toMultilinearSection MixedSection.fromMultilinearSection
    change
      (MixedSection.eval₀ (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) 1) =
        metricCcTensorFib (I := I) g x
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [ccTensorBilin_apply]
  unfold ccTensorModel
  rw [hround]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor_apply

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
