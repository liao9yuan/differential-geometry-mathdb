import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Defs

import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.Decomposition
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import Submission.DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Integral.L2

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorRSNormedAddCommGroupOfRiemannianBundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.tensorRSNormedAddCommGroupOfRiemannianBundle target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma iterCovGrad_unit_eq_iterCov
    (h gBase : SmoothRiemannianMetric I M) (j : ℕ) :
    (fun x : M => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (2 + j) I x from
        (iteratedCovGrad (I := I) gBase 0 2 j
          (metricCcTensor (I := I) (M := M) gBase h)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
      (fun x : M => iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) h) j x) := by
  induction j with
  | zero =>
    funext x
    change (metricCcTensor (I := I) (M := M) gBase h).toSection x
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SBundle.metricTensorField (I := I) h x
    have h1 :
        (metricCcTensor (I := I) (M := M) gBase h).toSection x
            (unitZeroSec (I := I) (M := M) x) =
          metricCcTensorFib (I := I) h x := by
      rw [show (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
          ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) from rfl,
        ← ccTensorMultilinear_apply (I := I) gBase
          (metricCcTensor (I := I) (M := M) gBase h) x]
      let _ := Tensor0SBundle.tensor0SBundleTopology
        (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
      unfold ccTensorMultilinear metricCcTensor
      unfold MixedSection.toMultilinearSection MixedSection.fromMultilinearSection
      change
        (MixedSection.eval₀ (𝕜 := ℝ) (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
            (metricCcTensorFib (I := I) h x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) 1) =
          metricCcTensorFib (I := I) h x
      rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
        ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    rw [h1]
    ext m
    rw [metricCcTensorFib_apply, Tensor0SBundle.metricTensorField_apply]
  | succ j ih =>
    funext x
    set Tj : SmoothCcTensor gBase 0 (2 + j) :=
      iteratedCovGrad (I := I) gBase 0 2 j
        (metricCcTensor (I := I) (M := M) gBase h) with hTj
    change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace ((2 + j) + 1) I x from
        (covGrad (I := I) (M := M) gBase 0 (2 + j) Tj).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) (j + 1) x
    apply Tensor0SBundle.tensor0SSpace_ext (I := I) (2 + j + 1) x
    intro v
    change Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace ((2 + j) + 1) I x from
          (covGrad (I := I) (M := M) gBase 0 (2 + j) Tj).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.eval
        (iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) h) (j + 1) x) v
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (v 0)
    have hcons : v = Fin.cons (v 0) (Matrix.vecTail v) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k; simp [Matrix.vecTail]
    rw [covGrad_apply_unit_eval (I := I) (M := M) gBase (2 + j) Tj x v]
    rw [tensorCovDerivAt_def (I := I) (M := M) gBase 0 (2 + j) Tj x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0)),
      ContinuousLinearEquiv.symm_apply_apply]
    rw [covDeriv_unit_eval_eq (I := I) (M := M) gBase (2 + j) (Tj.toSection) x (v 0)]
    rw [ih]
    rw [← hXx]
    rw [← nabla0SFun_eq_tensor0SCovariantDerivative (I := I) gBase (2 + j) X
      (iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j) x]
    rw [iterCov_succ, covStep_apply]
    have hcons2 : v = Fin.cons (X x) (Matrix.vecTail v) := by rw [hXx]; exact hcons
    conv_rhs => rw [hcons2]
    rw [totalNabla0SFun_eval_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + j) (leviCivitaConnectionOfMetric (I := I) gBase) X
      (iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j) x
      (Matrix.vecTail v)]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.iterCovGrad_unit_eq_iterCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_unit_eq_iterCov target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] in
private lemma lowerAllUpper_zero_eq_unit
    (gBase : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor gBase 0 s) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (unitZeroSec (I := I) (M := M) x)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lowerAllUpper_zero_eq_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lowerAllUpper_zero_eq_unit target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] in
private lemma riemannianFiberNormSq_eq_normSq0S_unit
    (gBase : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (W : SmoothCcTensor gBase 0 s) :
    riemannianFiberNormSq (I := I) (M := M) gBase 0 s x (W.toSection x) =
      Tensor0SBundle.normSq0S (I := I) gBase x s
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gBase x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) gBase 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) gBase 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + s) gBase x
        (lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) gBase x (0 + s)
    basis hON _ _]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gBase x s basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) gBase basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm)
      (finCongr (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from by
        with_unfolding_all rfl))) _ _ ?_
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  rw [lowerAllUpper_zero_eq_unit (I := I) gBase s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Function.comp_apply];
     congr 1;
     apply Fin.ext;
     simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_eq_normSq0S_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_eq_normSq0S_unit target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace
  Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixedInstNormedSpace in
theorem normBridge (h gBase : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) gBase 0 (2 + j)
    ‖((iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h)).toSection x :
        TensorRSSpace 0 (2 + j) I x)‖ =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (j + 2)
        (metricCovDeriv (I := I) h gBase j x)) := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) gBase 0 (2 + j)
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gBase x
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I) gBase x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) gBase basis hON
  rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + j) x
    (iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h))]
  rw [riemannianFiberNormSq_eq_normSq0S_unit (I := I) gBase (2 + j) x
    (iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h))]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (2 + j) I x from
        (iteratedCovGrad gBase 0 2 j
          (metricCcTensor (I := I) (M := M) gBase h)).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j x from
    congrFun (iterCovGrad_unit_eq_iterCov (I := I) h gBase j) x]
  rw [show Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (j + 2)
        (metricCovDeriv (I := I) h gBase j x)) =
      metricCovDerivNorm (I := I) j h gBase x from rfl]
  rw [metricCovDerivNorm_eq_iterCov (I := I) h gBase j basis hinv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.normBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.normBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.normBridge ``Submission.DifferentialGeometry.PDE.RicciFlow.normBridge

end RicciFlow
end PDE
end DifferentialGeometry
