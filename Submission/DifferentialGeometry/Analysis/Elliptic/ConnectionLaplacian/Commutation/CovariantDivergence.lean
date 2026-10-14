import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.Divergence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.RoughLaplacianCometricTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SlotExtension.Parallelism
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Pointwise.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.AllOrder
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.HomFieldActionL2JetBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem covGrad_operatorFieldApplication_cometricDoubleTrace_eq (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (W : SmoothCcTensor g₀ 0 (p + 2)) :
    covGrad (I := I) (M := M) g₀ 0 p
        (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)
          W) =
      operatorFieldApply (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
        (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p))
        (covGrad (I := I) (M := M) g₀ 0 (p + 2) W) := by
  rw [covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ (p + 2) p
    (cometricDoubleTraceField (I := I) g₀ p) W]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ p]
  exact add_eq_right.mpr (operatorFieldApplication_zero_left (I := I) (M := M) g₀ (p + 2) (p + 1) W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_operatorFieldApplication_cometricDoubleTrace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_operatorFieldApplication_cometricDoubleTrace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_operatorFieldApplication_cometricDoubleTrace_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_operatorFieldApplication_cometricDoubleTrace_eq

omit [SigmaCompactSpace M] in
theorem covGrad_covGrad_operatorFieldApplication_cometricDoubleTrace_eq (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (W : SmoothCcTensor g₀ 0 (p + 2)) :
    covGrad (I := I) (M := M) g₀ 0 (p + 1)
        (covGrad (I := I) (M := M) g₀ 0 p
          (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p
            (cometricDoubleTraceField (I := I) g₀ p) W)) =
      operatorFieldApply (I := I) (M := M) g₀ (p + 2 + 1 + 1) (p + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
          (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)))
        (covGrad (I := I) (M := M) g₀ 0 (p + 2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 (p + 2) W)) := by
  rw [covGrad_operatorFieldApplication_cometricDoubleTrace_eq (I := I) (M := M) g₀ p W]
  rw [covGrad_operatorFieldApply_eq (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
    (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p))
    (covGrad (I := I) (M := M) g₀ 0 (p + 2) W)]
  rw [covGrad_slotExtend_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ (p + 2) p
    (cometricDoubleTraceField (I := I) g₀ p)
    (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ p)]
  exact add_eq_right.mpr (operatorFieldApplication_zero_left (I := I) (M := M) g₀ (p + 2 + 1) (p + 1 + 1)
    (covGrad (I := I) (M := M) g₀ 0 (p + 2) W))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covGrad_covGrad_operatorFieldApplication_cometricDoubleTrace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covGrad_covGrad_operatorFieldApplication_cometricDoubleTrace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covGrad_covGrad_operatorFieldApplication_cometricDoubleTrace_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covGrad_covGrad_operatorFieldApplication_cometricDoubleTrace_eq

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_toModel_unitEval_gen
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g₀ 0 s) (x : M)
    (v : Fin s → E) :
    unitModel (I := I) (M := M) g₀ s W x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.unitModel_eq_toModel_unitEval_gen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.unitModel_eq_toModel_unitEval_gen target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma unitModel_operatorFieldApplication_cometricDoubleTrace_eq_dualTrace
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (W : SmoothCcTensor g₀ 0 (p + 2))
    (x : M) (v : Fin p → E) :
    unitModel (I := I) (M := M) g₀ p
        (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)
          W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (p + 2) W x
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (p + 2) I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g₀ p).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (p + 2) I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) p (cometricLmodel (I := I) g₀ x)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.unitModel_operatorFieldApplication_cometricDoubleTrace_eq_dualTrace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.unitModel_operatorFieldApplication_cometricDoubleTrace_eq_dualTrace target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma secondCovDeriv_frame_unitEval_eq_iteratedCovGrad_gen
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 t) (x : M)
    (v : Fin t → E) (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g₀ 0 t
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => W.toSection z) x)
          (unitZeroSec (I := I) (M := M) x)) v =
      unitModel (I := I) (M := M) g₀ (t + 2) (iteratedCovGrad (I := I) g₀ 0 t 2 W) x
        (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x))
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x)) v)) := by
  have hbridge := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval
    (I := I) (M := M) g₀ t W
    (X := smoothOrthoFrame (I := I) g₀ x i)
    (Y := smoothOrthoFrame (I := I) g₀ x i)
    (smoothOrthoFrame_smooth (I := I) g₀ x i) (smoothOrthoFrame_smooth (I := I) g₀ x i) x v
  exact hbridge.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.secondCovDeriv_frame_unitEval_eq_iteratedCovGrad_gen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.secondCovDeriv_frame_unitEval_eq_iteratedCovGrad_gen target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
lemma unitModel_rawConnLap_eq_frame_sum_covariantTensor
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 t) (x : M)
    (v : Fin t → E) :
    unitModel (I := I) (M := M) g₀ t (rawTensorConnLapSmooth (I := I) g₀ 0 t W) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (t + 2) (iteratedCovGrad (I := I) g₀ 0 t 2 W) x
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x))
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₀ x i x)) v)) := by
  classical
  rw [unitModel_eq_toModel_unitEval_gen]
  have hsec : (rawTensorConnLapSmooth (I := I) g₀ 0 t W).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g₀ 0 t
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => W.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g₀ 0 t W x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g₀ 0 t
        (fun z : M => W.toSection z) x]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        (rawTensorConnLapSmooth (I := I) g₀ 0 t W).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g₀ 0 t
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => W.toSection z) x)
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, sum_apply]]
  rw [← Tensor0SSpace.toModelL_apply (s := t) (x := x),
    map_sum (Tensor0SSpace.toModelL t x)]
  simp only [sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  exact secondCovDeriv_frame_unitEval_eq_iteratedCovGrad_gen (I := I) g₀ t W x v i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.unitModel_rawConnLap_eq_frame_sum_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.unitModel_rawConnLap_eq_frame_sum_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.unitModel_rawConnLap_eq_frame_sum_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.unitModel_rawConnLap_eq_frame_sum_covariantTensor

omit [SigmaCompactSpace M] in
theorem rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 t) :
    rawTensorConnLapSmooth (I := I) g₀ 0 t W =
      operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
        (iteratedCovGrad (I := I) g₀ 0 t 2 W) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_rawConnLap_eq_frame_sum_covariantTensor (I := I) g₀ t W x v,
    unitModel_operatorFieldApplication_cometricDoubleTrace_eq_dualTrace (I := I) g₀ t
      (iteratedCovGrad (I := I) g₀ 0 t 2 W) x v]
  exact
    (cometric_dualTrace_eq_orthoFrame_diag
    (I := I) g₀ (s := t) x
    (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
    (unitModel (I := I) (M := M) g₀ (t + 2) (iteratedCovGrad (I := I) g₀ 0 t 2 W) x) v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_contract_covariant_eval (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          Tensor0SBundle.contractCovariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b v) m) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_contract_covariant_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.toModel_contract_covariant_eval target :: scope.openDecls } }

private lemma vecTail_cons_eq {α : Type*} {n : ℕ} (a : α) (w : Fin n → α) :
    Matrix.vecTail (Fin.cons a w) = w := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.vecTail_cons_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.vecTail_cons_eq target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem covDivergence_eq_cometricDoubleTrace_apply_covGrad
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) :
    covDivergence (I := I) (M := M) g₀ s V =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_operatorFieldApplication_cometricDoubleTrace_eq_dualTrace (I := I) g₀ s
    (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x v]
  rw [show ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x
        (Fin.cons (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x))
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₀ x i x)) v)) from
    cometric_dualTrace_eq_orthoFrame_diag
      (I := I) g₀ (s := s) x
      (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
      (unitModel (I := I) (M := M) g₀ (s + 2) (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x) v]
  rw [unitModel_eq_toModel_unitEval_gen]
  have hsec : (covDivergence (I := I) (M := M) g₀ s V).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covDivergenceBilinear (I := I) (M := M) g₀ s V x
          (smoothOrthoFrame (I := I) g₀ x i x) (smoothOrthoFrame (I := I) g₀ x i x) := by
    rw [covDivergence_toSection_apply]
    rfl
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s) I x from
        (covDivergence (I := I) (M := M) g₀ s V).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          covDivergenceBilinear (I := I) (M := M) g₀ s V x
            (smoothOrthoFrame (I := I) g₀ x i x) (smoothOrthoFrame (I := I) g₀ x i x))
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, sum_apply]]
  rw [← Tensor0SSpace.toModelL_apply (s := s) (x := x),
    map_sum (Tensor0SSpace.toModelL s x)]
  simp only [sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g₀ x i z)) x :=
    (smoothOrthoFrame_smooth (I := I) g₀ x i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g₀ s V x hSmooth_at hSmooth_at]
  rw [toModel_contract_covariant_eval (I := I) (M := M) s x
    (smoothOrthoFrame (I := I) g₀ x i x)
    ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
        (LeviCivita (I := I) g₀)).toFun (fun z : M => V.toSection z) x
      (smoothOrthoFrame (I := I) g₀ x i x))
    (unitZeroSec (I := I) (M := M) x) v]
  rw [show unitModel (I := I) (M := M) g₀ (s + 2)
      (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) x
      (Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) g₀ x i x))
        (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x)) v)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (covGrad (I := I) (M := M) g₀ 0 (s + 1) V).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x))
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x)) v)) from rfl]
  rw [Tensor0SSpace.toModel_apply_model_vector,
    Tensor0SSpace.toModel_apply_model_vector]
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
          (LeviCivita (I := I) g₀)).toFun (fun z : M => V.toSection z) x
            (smoothOrthoFrame (I := I) g₀ x i x))
        (unitZeroSec (I := I) (M := M) x))
      (Fin.cons (smoothOrthoFrame (I := I) g₀ x i x)
        (fun j => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v j))) =
    Tensor0SSpace.eval
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (covGrad (I := I) (M := M) g₀ 0 (s + 1) V).toSection x)
        (unitZeroSec (I := I) (M := M) x))
      (Fin.cons (smoothOrthoFrame (I := I) g₀ x i x)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ x i x)
          (fun j => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v j))))
  have hcov := covGrad_apply_unit_eval (I := I) (M := M) g₀ (s + 1) V x
    (Fin.cons (smoothOrthoFrame (I := I) g₀ x i x)
      (Fin.cons (smoothOrthoFrame (I := I) g₀ x i x)
        (fun j => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v j))))
  rw [tensorCovDerivAt_def] at hcov
  simpa only [ContinuousLinearEquiv.symm_apply_apply, vecTail_cons_eq,
    Fin.cons_zero] using hcov.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergence_eq_cometricDoubleTrace_apply_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergence_eq_cometricDoubleTrace_apply_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergence_eq_cometricDoubleTrace_apply_covGrad ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergence_eq_cometricDoubleTrace_apply_covGrad

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem l2Inner_sub_left_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  have hsub : (S₁.toFun - S₂.toFun) = S₁.toFun + (-1 : ℝ) • S₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S₂.toFun x) (T.toFun x)) := by
      funext x
      change tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • S₂.toFun x) (T.toFun x) = _
      rw [tensorInnerPointwise_smul_left]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun ((-1 : ℝ) • S₂.toFun) T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T) hint2,
    tensorL2Inner_smul_left]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.l2Inner_sub_left_cc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.l2Inner_sub_left_cc target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem l2Inner_sub_right_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  have hsub : (T₁.toFun - T₂.toFun) = T₁.toFun + (-1 : ℝ) • T₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S T₂
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (T₂.toFun x)) := by
      funext x
      change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) ((-1 : ℝ) • T₂.toFun x) = _
      rw [tensorInnerPointwise_smul_right]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_right (I := I) (M := M) g r s S.toFun T₁.toFun ((-1 : ℝ) • T₂.toFun)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S T₁) hint2,
    tensorL2Inner_smul_right]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.l2Inner_sub_right_cc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.l2Inner_sub_right_cc target :: scope.openDecls } }

omit [CompactSpace M] in
theorem rawTensorConnLapSmooth_l2Inner_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
  have hTv := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s T v
  have hvT := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s v T
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T).toFun (covGrad (I := I) (M := M) g r s v).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s v).toFun T.toFun
  rw [hsymm1, hvT] at hTv
  rw [← hsymm2]
  linarith [hTv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_l2Inner_selfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_l2Inner_selfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_l2Inner_selfAdjoint ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_l2Inner_selfAdjoint

omit [CompactSpace M] in
theorem pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : SmoothCcTensor g 0 s) (Z : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s X).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g 0 s X.toFun
        (rawTensorConnLapSmooth (I := I) g 0 s (covDivergence (I := I) (M := M) g s Z) -
          covDivergence (I := I) (M := M) g s
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun := by
  classical
  have hptc : (pointwiseTensorCurv (I := I) (M := M) g s X).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s X)).toFun -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s X)).toFun := by
    unfold pointwiseTensorCurv
    rw [SmoothCcTensor.toFun_sub]
  have hK : (rawTensorConnLapSmooth (I := I) g 0 s (covDivergence (I := I) (M := M) g s Z) -
      covDivergence (I := I) (M := M) g s
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 s
          (covDivergence (I := I) (M := M) g s Z)).toFun -
        (covDivergence (I := I) (M := M) g s
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun :=
    SmoothCcTensor.toFun_sub _ _
  rw [hptc, hK]
  rw [l2Inner_sub_left_cc (I := I) (M := M) g 0 (s + 1)
    (rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s X))
    (covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s X)) Z]
  rw [l2Inner_sub_right_cc (I := I) (M := M) g 0 s X
    (rawTensorConnLapSmooth (I := I) g 0 s (covDivergence (I := I) (M := M) g s Z))
    (covDivergence (I := I) (M := M) g s (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z))]
  have h1 : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s X)).toFun Z.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s X.toFun
        (covDivergence (I := I) (M := M) g s
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)).toFun := by
    rw [rawTensorConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s X) Z]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g s X (rawTensorConnLapSmooth (I := I) g 0 (s + 1) Z)
  have h2 : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s X)).toFun Z.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s X.toFun
        (rawTensorConnLapSmooth (I := I) g 0 s
          (covDivergence (I := I) (M := M) g s Z)).toFun := by
    rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g s (rawTensorConnLapSmooth (I := I) g 0 s X) Z]
    rw [rawTensorConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g 0 s
      X (covDivergence (I := I) (M := M) g s Z)]
  linarith [h1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator ``Submission.DifferentialGeometry.Analysis.Elliptic.pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma unitModel_operatorFieldApplication_slotExtend_slotExtend_cometric
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (U : SmoothCcTensor g₀ 0 (t + 4))
    (x : M) (a b : E) (v : Fin t → E) :
    unitModel (I := I) (M := M) g₀ (t + 2)
        (operatorFieldApply (I := I) (M := M) g₀ (t + 4) (t + 2)
          (slotExtend (I := I) (M := M) g₀ (t + 2 + 1) (t + 1)
            (slotExtend (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)))
          U) x
        (Fin.cons a (Fin.cons b v)) =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ (t + 4) U x
          (Fin.cons a (Fin.cons b
            (Fin.cons (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)))) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace (t + 4) I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (slotExtend (I := I) (M := M) g₀ (t + 2 + 1) (t + 1)
          (slotExtend (I := I) (M := M) g₀ (t + 2) t
            (cometricDoubleTraceField (I := I) g₀ t))).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 4) I x from
          U.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace (t + 4) I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (slotExtend (I := I) (M := M) g₀ (t + 2 + 1) (t + 1)
          (slotExtend (I := I) (M := M) g₀ (t + 2) t
            (cometricDoubleTraceField (I := I) g₀ t))).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 4) I x from
          U.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [slotExtend_toSection, slotExtendFib_apply_eval]
  rw [slotExtend_toSection, slotExtendFib_apply_eval]
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) t (cometricLmodel (I := I) g₀ x)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)]
  rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.unitModel_operatorFieldApplication_slotExtend_slotExtend_cometric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.unitModel_operatorFieldApplication_slotExtend_slotExtend_cometric target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem iteratedCovGrad_two_operatorFieldApplication_cometricDoubleTrace_eq
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (W : SmoothCcTensor g₀ 0 (p + 2)) :
    iteratedCovGrad (I := I) g₀ 0 p 2
        (operatorFieldApply (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)
          W) =
      operatorFieldApply (I := I) (M := M) g₀ (p + 2 + 1 + 1) (p + 1 + 1)
        (slotExtend (I := I) (M := M) g₀ (p + 2 + 1) (p + 1)
          (slotExtend (I := I) (M := M) g₀ (p + 2) p (cometricDoubleTraceField (I := I) g₀ p)))
        (iteratedCovGrad (I := I) g₀ 0 (p + 2) 2 W) :=
  covGrad_covGrad_operatorFieldApplication_cometricDoubleTrace_eq (I := I) (M := M) g₀ p W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.iteratedCovGrad_two_operatorFieldApplication_cometricDoubleTrace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.iteratedCovGrad_two_operatorFieldApplication_cometricDoubleTrace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.iteratedCovGrad_two_operatorFieldApplication_cometricDoubleTrace_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.iteratedCovGrad_two_operatorFieldApplication_cometricDoubleTrace_eq

omit [SigmaCompactSpace M] in
theorem rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (W : SmoothCcTensor g₀ 0 (t + 2)) :
    rawTensorConnLapSmooth (I := I) g₀ 0 t
        (operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
          W) =
      operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t)
        (rawTensorConnLapSmooth (I := I) g₀ 0 (t + 2) W) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_rawConnLap_eq_frame_sum_covariantTensor (I := I) g₀ t
    (operatorFieldApply (I := I) (M := M) g₀ (t + 2) t (cometricDoubleTraceField (I := I) g₀ t) W) x
      v]
  rw [unitModel_operatorFieldApplication_cometricDoubleTrace_eq_dualTrace (I := I) g₀ t
    (rawTensorConnLapSmooth (I := I) g₀ 0 (t + 2) W) x v]
  have hlhs : ∀ i : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ (t + 2)
          (iteratedCovGrad (I := I) g₀ 0 t 2
            (operatorFieldApply (I := I) (M := M) g₀ (t + 2) t
              (cometricDoubleTraceField (I := I) g₀ t) W)) x
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x))
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₀ x i x)) v)) =
        ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ (t + 4)
            (iteratedCovGrad (I := I) g₀ 0 (t + 2) 2 W) x
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₀ x i x))
              (Fin.cons
                (tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (smoothOrthoFrame (I := I) g₀ x i x))
                (Fin.cons (cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v)))) := by
    intro i
    rw [iteratedCovGrad_two_operatorFieldApplication_cometricDoubleTrace_eq (I := I) (M := M) g₀ t W]
    exact unitModel_operatorFieldApplication_slotExtend_slotExtend_cometric (I := I) (M := M) g₀ t
      (iteratedCovGrad (I := I) g₀ 0 (t + 2) 2 W) x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (smoothOrthoFrame (I := I) g₀ x i x))
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (smoothOrthoFrame (I := I) g₀ x i x)) v
  have hrhs : ∀ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ (t + 2)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (t + 2) W) x
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) =
        ∑ i : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ (t + 4)
            (iteratedCovGrad (I := I) g₀ 0 (t + 2) 2 W) x
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₀ x i x))
              (Fin.cons
                (tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (smoothOrthoFrame (I := I) g₀ x i x))
                (Fin.cons (cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v)))) := by
    intro k
    exact unitModel_rawConnLap_eq_frame_sum_covariantTensor (I := I) g₀ (t + 2) W x
      (Fin.cons (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) v))
  rw [Finset.sum_congr rfl (fun i _ => hlhs i), Finset.sum_congr rfl (fun k _ => hrhs k)]
  rw [Finset.sum_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm

omit [SigmaCompactSpace M] in
theorem rawConnLap_covDivergence_commutator_eq_operatorFieldApplication_pointwiseTensorCurv
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (Z : SmoothCcTensor g₀ 0 (s + 1)) :
    rawTensorConnLapSmooth (I := I) g₀ 0 s (covDivergence (I := I) (M := M) g₀ s Z) -
        covDivergence (I := I) (M := M) g₀ s
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) Z) := by
  have h1 : rawTensorConnLapSmooth (I := I) g₀ 0 s (covDivergence (I := I) (M := M) g₀ s Z) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 2)
          (covGrad (I := I) (M := M) g₀ 0 (s + 1) Z)) := by
    rw [covDivergence_eq_cometricDoubleTrace_apply_covGrad (I := I) (M := M) g₀ s Z]
    exact rawTensorConnLapSmooth_cometricDoubleTrace_apply_comm (I := I) (M := M) g₀ s
      (covGrad (I := I) (M := M) g₀ 0 (s + 1) Z)
  have h2 : covDivergence (I := I) (M := M) g₀ s
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z) =
      operatorFieldApply (I := I) (M := M) g₀ (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
        (covGrad (I := I) (M := M) g₀ 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z)) :=
    covDivergence_eq_cometricDoubleTrace_apply_covGrad (I := I) (M := M) g₀ s
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z)
  rw [h1, h2]
  rw [← operatorFieldApplication_sub_right (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawConnLap_covDivergence_commutator_eq_operatorFieldApplication_pointwiseTensorCurv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawConnLap_covDivergence_commutator_eq_operatorFieldApplication_pointwiseTensorCurv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawConnLap_covDivergence_commutator_eq_operatorFieldApplication_pointwiseTensorCurv ``Submission.DifferentialGeometry.Analysis.Elliptic.rawConnLap_covDivergence_commutator_eq_operatorFieldApplication_pointwiseTensorCurv

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_iteratedCovGrad_comp_cc (g : SmoothRiemannianMetric I M) (s j i : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ := by
  have hsq : ‖iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M), SmoothCcTensor.norm_def (I := I) (M := M),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0
        ((s + j) + i)
        (iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0
        (s + (j + i)) (iteratedCovGrad (I := I) g 0 s (j + i) S)]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g 0 s j i S x
  have ha : (0 : ℝ) ≤
      ‖iteratedCovGrad (I := I) g 0 (s + j) i (iteratedCovGrad (I := I) g 0 s j S)‖ :=
    norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ := norm_nonneg _
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, hsq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.norm_iteratedCovGrad_comp_cc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.norm_iteratedCovGrad_comp_cc target :: scope.openDecls } }

theorem exists_iteratedCovGrad_covDivergence_l2_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)),
        ‖iteratedCovGrad (I := I) g₀ 0 s p (covDivergence (I := I) (M := M) g₀ s V)‖ ≤
          K p * ∑ k ∈ Finset.range (p + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) k V‖ := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_operatorFieldApplication_iteratedCovGrad_l2_window_bound (I := I) (M := M) g₀ (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s)
  refine ⟨cc, hcc_nn, fun p V => ?_⟩
  rw [covDivergence_eq_cometricDoubleTrace_apply_covGrad (I := I) (M := M) g₀ s V]
  refine le_trans (hcc (covGrad (I := I) (M := M) g₀ 0 (s + 1) V) p) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hcc_nn p)
  have hterm : ∀ i ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 2) i (covGrad (I := I) (M := M) g₀ 0 (s + 1) V)‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (1 + i) V‖ := by
    intro i _
    have h0 : covGrad (I := I) (M := M) g₀ 0 (s + 1) V =
        iteratedCovGrad (I := I) g₀ 0 (s + 1) 1 V := rfl
    rw [h0]
    exact norm_iteratedCovGrad_comp_cc (I := I) (M := M) g₀ (s + 1) 1 i V
  rw [Finset.sum_congr rfl hterm]
  have hreindex : ∑ i ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (1 + i) V‖ =
      ∑ i ∈ Finset.range (p + 1), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (i + 1) V‖ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.add_comm 1 i]
  rw [hreindex]
  have hshift := Finset.sum_range_succ'
    (fun k => ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) k V‖) (p + 1)
  have h0nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) 0 V‖ := norm_nonneg _
  linarith [hshift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_covDivergence_l2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_covDivergence_l2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_covDivergence_l2_le ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_covDivergence_l2_le

section CurvatureCommutatorL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (Z : SmoothCcTensor g₀ 0 (s + 1)),
        ‖iteratedCovGrad (I := I) g₀ 0 s p
            (rawTensorConnLapSmooth (I := I) g₀ 0 s (covDivergence (I := I) (M := M) g₀ s Z) -
              covDivergence (I := I) (M := M) g₀ s
                (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Z))‖ ≤
          K p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) a Z‖ := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_operatorFieldApplication_iteratedCovGrad_l2_window_bound (I := I) (M := M) g₀ (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s)
  obtain ⟨Kp, hKp_nn, hKp⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ (s + 1)
  refine ⟨fun p => cc p * ∑ i ∈ Finset.range (p + 1), Kp i,
    fun p => mul_nonneg (hcc_nn p) (Finset.sum_nonneg (fun i _ => hKp_nn i)),
    fun p Z => ?_⟩
  rw [rawConnLap_covDivergence_commutator_eq_operatorFieldApplication_pointwiseTensorCurv (I := I) (M := M) g₀ s Z]
  refine le_trans (hcc (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) Z) p) ?_
  have hJ_nn : (0 : ℝ) ≤ ∑ a ∈ Finset.range (p + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) a Z‖ :=
    Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hterm : ∀ i ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 2) i
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + 1) Z)‖ ≤
        Kp i * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) a Z‖ := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine le_trans (hKp i Z) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKp_nn i)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => norm_nonneg _)
    exact Finset.range_subset_range.mpr (by omega)
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (hcc_nn p)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le

end CurvatureCommutatorL2

omit [SigmaCompactSpace M] in
theorem covDiv_operatorFieldApply (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 1 1) (W : SmoothCcTensor g₀ 0 1) :
    covDivergence (I := I) (M := M) g₀ 0
        (operatorFieldApply (I := I) (M := M) g₀ 1 1 Φ W) =
      operatorFieldApply (I := I) (M := M) g₀ 1 0
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 0
            (cometricDoubleTraceField (I := I) g₀ 0)
            (covGrad (I := I) (M := M) g₀ 1 1 Φ)) W +
        operatorFieldApply (I := I) (M := M) g₀ 2 0
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 0
            (cometricDoubleTraceField (I := I) g₀ 0)
            (slotExtend (I := I) (M := M) g₀ 1 1 Φ))
          (covGrad (I := I) (M := M) g₀ 0 1 W) := by
  rw [covDivergence_eq_cometricDoubleTrace_apply_covGrad, covGrad_operatorFieldApply_eq,
    operatorFieldApplication_add_right]
  rw [operatorFieldApplication_assoc, operatorFieldApplication_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDiv_operatorFieldApply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDiv_operatorFieldApply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDiv_operatorFieldApply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDiv_operatorFieldApply

end Elliptic
end Analysis
end DifferentialGeometry

end
