import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Weitzenbock
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.Field
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.SlotFree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Integral.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def gradSlotCurvCoeff
    (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from
          TensorRSSpace.ofCLM
            (slotFreeCurvOpFib (I := I) (M := M) g₀ 2 x))
      contMDiff_toFun :=
        slotFreeCurvOpFib_contMDiff (I := I) (M := M) g₀ 2 }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurvCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurvCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurvCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurvCoeff

omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem gradSlotCurv_apply
    (g₀ : SmoothRiemannianMetric I M) (x : M) :
    (gradSlotCurvCoeff (I := I) (M := M) g₀).toSection x =
      (show TensorRSSpace 2 4 I x from
        TensorRSSpace.ofCLM
          (slotFreeCurvOpFib (I := I) (M := M) g₀ 2 x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_apply

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem gradSlotCurv_eval
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (u w : TangentSpace I x)
    (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (gradSlotCurvCoeff (I := I) (M := M) g₀).toSection x) A)
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin 2, Tensor0SSpace.toModel A
          (Function.update m k
            (riemannOp (LeviCivita (I := I) g₀) x u w (m k))) := by
  rw [gradSlotCurv_apply]
  exact slotFreeCurvOpFib_apply_eval (I := I) (M := M) g₀ 2 x A u w m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_eval ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_eval

omit [SigmaCompactSpace M] in
theorem gradSlot_cov_eval
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (d u w : TangentSpace I x)
    (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (covGrad (I := I) (M := M) g₀ 2 4
            (gradSlotCurvCoeff (I := I) (M := M) g₀)).toSection x) A)
        (Fin.cons d (Fin.cons u (Fin.cons w m))) =
      - ∑ k : Fin 2, Tensor0SSpace.toModel A
          (Function.update m k
            (nablaRiemannOp (I := I) g₀ x d u w (m k))) := by
  have h := covGrad_toSection_apply_eval (I := I) (M := M) g₀ 2 4
    (gradSlotCurvCoeff (I := I) (M := M) g₀) x A
    (Fin.cons d (Fin.cons u (Fin.cons w m)))
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (covGrad (I := I) (M := M) g₀ 2 4
          (gradSlotCurvCoeff (I := I) (M := M) g₀)).toSection x) A)
      (Fin.cons d (Fin.cons u (Fin.cons w m))) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 2 4
          (gradSlotCurvCoeff (I := I) (M := M) g₀) x d) A)
      (Fin.cons u (Fin.cons w m)) at h
  rw [h]
  change Tensor0SSpace.toModel
      (TensorRSSpace.toCLM
        (tensorCovDerivAt (I := I) (M := M) g₀ 2 4
          (gradSlotCurvCoeff (I := I) (M := M) g₀) x (show E from d)) A)
      (Fin.cons u (Fin.cons w m)) = _
  rw [tensorCovDerivAt_def]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 2 4
          (LeviCivita (I := I) g₀)
          (slotFreeOpCc (I := I) (M := M) g₀ 2).toSection x d) A)
      (Fin.cons u (Fin.cons w m)) = _
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 2 4
          (LeviCivita (I := I) g₀)
          (slotFreeOpCc (I := I) (M := M) g₀ 2).toSection x d) A)
      (Fin.cons u (Fin.cons w m)) =
    - ∑ k : Fin 2, Tensor0SSpace.eval A
        (Function.update m k
          (nablaRiemannOp (I := I) g₀ x d u w (m k)))
  exact slotFree_cov_eval (I := I) (M := M) g₀ 2 x d A u w m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_cov_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_cov_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_cov_eval ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_cov_eval

omit [SigmaCompactSpace M] in
theorem gradSlotCurv_spec
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    iteratedCovGrad (I := I) g₀ 0 2 2 S -
        domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
        (gradSlotCurvCoeff (I := I) (M := M) g₀) S := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub (I := I) g₀ 4 _ _ x, sub_apply,
    domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (iteratedCovGrad (I := I) g₀ 0 2 2 S) x,
    ContinuousMultilinearMap.domDomCongr_apply]
  set Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0),
      smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hXs_def
  set Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1),
      smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩ with hYs_def
  have hXx : Xs x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYx : Ys x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  set m : Fin 2 → TangentSpace I x := ![v 2, v 3] with hm_def
  have hv_eq : v = Fin.cons (Xs x) (Fin.cons (Ys x) m) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> rfl
  have hv_swap : (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Fin.cons (Ys x) (Fin.cons (Xs x) m) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> rfl
  have h1 : unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    conv_lhs => rw [hv_eq]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval
      (I := I) (M := M) g₀ 2 S Xs.contMDiff Ys.contMDiff x m
  have h2 : unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    rw [hv_swap]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval
      (I := I) (M := M) g₀ 2 S Ys.contMDiff Xs.contMDiff x m
  have h3 : tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x -
      tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
        (fun y : M => S.toSection y) x =
      riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x :=
    tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g₀ 0 2
      (fun y : M => S.toSection y)
      ((Xs.contMDiff x).mdifferentiableAt (by simp))
      ((Ys.contMDiff x).mdifferentiableAt (by simp))
  have h4 : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m := by
    change Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m -
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m
    have h3eval := congrArg
      (fun L : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x =>
        Tensor0SSpace.eval (L (unitZeroSec (I := I) (M := M) x)) m) h3
    simpa only [sub_apply, Tensor0SSpace.eval_sub] using h3eval
  have h5 := riemannSec_tensorCov_apply_eval (I := I) (M := M) g₀ 0 2 Xs Ys
    S.toSection (unitZeroSec (I := I) (M := M)) x m
  have h6 : riemannSec
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀))
      (fun b => Xs b) (fun b => Ys b) (fun b => unitZeroSec (I := I) (M := M) b) x = 0 :=
    riemannSec_tensor0SCov_zero_eq_zero (I := I) g₀ Xs Ys
      (fun b => unitZeroSec (I := I) (M := M) b)
      (contMDiff_unitZeroSection (I := I) (M := M)) x
  have h7 := riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g₀ 2 Xs Ys
    (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
      (unitZeroSec (I := I) (M := M) b))
    (contMDiff_unitEvalSection (I := I) (M := M) g₀ 2 S) x m
  have h8 : ∀ u : TangentSpace I x, baseSlotCurv (I := I) g₀ Xs Ys x u =
      riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) u := by
    intro u
    rw [show baseSlotCurv (I := I) g₀ Xs Ys x u =
        riemannSec (LeviCivita (I := I) g₀) (fun b => Xs b) (fun b => Ys b)
          (fun b => smoothExtensionTangent (I := I) x u b) x from rfl]
    rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g₀)
      Xs.contMDiff Ys.contMDiff (smoothExtensionTangent_contMDiff (I := I) x u)]
    rw [smoothExtensionTangent_eq (I := I) x u, hXx, hYx]
  have h9 := slotFreeCurvOpFib_apply_eval (I := I) (M := M) g₀ 2 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v 0) (v 1) m
  have hv0 : v = Fin.cons (v 0) (Fin.cons (v 1) m) := by
    rw [hm_def]
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, h4, h5, h6, map_zero]
  change Tensor0SSpace.eval
      (riemannSec
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
        (fun b => Xs b) (fun b => Ys b)
        (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          S.toSection b) (unitZeroSec (I := I) (M := M) b)) x) m -
    Tensor0SSpace.eval (0 : Tensor0SSpace 2 I x) m = _
  rw [Tensor0SSpace.eval_zero, sub_zero, h7]
  rw [Finset.sum_congr rfl (fun k _ => by rw [h8 (m k)])]
  rw [← h9]
  conv_rhs => rw [unitModel, hv0]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_spec ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlotCurv_spec

omit [SigmaCompactSpace M] in
theorem gradSlot_sub_eq_curv
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : SmoothCcTensor g₀ 2 4,
      ∀ S : SmoothCcTensor g₀ 0 2,
        iteratedCovGrad (I := I) g₀ 0 2 2 S -
            domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C S :=
  ⟨gradSlotCurvCoeff (I := I) (M := M) g₀,
    gradSlotCurv_spec (I := I) (M := M) g₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_sub_eq_curv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_sub_eq_curv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_sub_eq_curv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_sub_eq_curv

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
