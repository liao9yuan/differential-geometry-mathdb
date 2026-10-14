import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.CovariantDerivativeQuadraticBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.ConvexPerturbationC2
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.CovariantTwoTensor.FiberNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.SingleSlotFiberNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connectionDifferenceCovDerivBiContrFib deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff deTurckLieCovariantDerivativeInsertionFib deTurckLieCovariantDerivativeInsertionFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnectionDifferenceCovDeriv connectionDifference_pairing_mdiffAt connectionDifferenceCovDerivOp deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPath convexPerturbation metricPerturbationPath_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one metricPerturbationPathDomain)
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
  (metric_inner_cauchy_schwarz_sq)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connectionDifference_gFibreNorm_le_iteratedCovGrad_of_lt_one deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel)
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnectionDifference_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DeTurckLieConnectionDifferenceDerivativeGridBrick

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma interiorProduct_toModel_eval_deTurckLieConnectionDifferenceDerivative (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x vv) w) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := ℝ) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.interiorProduct_toModel_eval_deTurckLieConnectionDifferenceDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.interiorProduct_toModel_eval_deTurckLieConnectionDifferenceDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.interiorProduct_toModel_eval_deTurckLieConnectionDifferenceDerivative ``Submission.DifferentialGeometry.Analysis.Sobolev.interiorProduct_toModel_eval_deTurckLieConnectionDifferenceDerivative

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_om_single_eq_cotangentToDual_deTurckLieConnectionDifferenceDerivative (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m =
      cotangentToDual (I := I) (x := x) om
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
  rw [show m = (fun _ : Fin 1 => m 0) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.toModel_om_single_eq_cotangentToDual_deTurckLieConnectionDifferenceDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.toModel_om_single_eq_cotangentToDual_deTurckLieConnectionDifferenceDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.toModel_om_single_eq_cotangentToDual_deTurckLieConnectionDifferenceDerivative ``Submission.DifferentialGeometry.Analysis.Sobolev.toModel_om_single_eq_cotangentToDual_deTurckLieConnectionDifferenceDerivative

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_eq_inner_sharp_deTurckLieConnectionDifferenceDerivative (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (ww : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om ww =
      g₀.inner x ww (inverseMetricSharpFib (I := I) g₀ x om) := by
  rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [show g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om) ww =
      cotangentToDualLinear (I := I) (x := x) om ww from by
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om ww]]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.cotangentToDual_eq_inner_sharp_deTurckLieConnectionDifferenceDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.cotangentToDual_eq_inner_sharp_deTurckLieConnectionDifferenceDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.cotangentToDual_eq_inner_sharp_deTurckLieConnectionDifferenceDerivative ``Submission.DifferentialGeometry.Analysis.Sobolev.cotangentToDual_eq_inner_sharp_deTurckLieConnectionDifferenceDerivative

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_map_sub_deTurckLieConnectionDifferenceDerivative (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (a - b) =
      cotangentToDual (I := I) (x := x) om a - cotangentToDual (I := I) (x := x) om b := by
  simp only [show ∀ v : TangentSpace I x, cotangentToDual (I := I) (x := x) om v =
      cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
  exact map_sub _ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_sub_deTurckLieConnectionDifferenceDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_sub_deTurckLieConnectionDifferenceDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_sub_deTurckLieConnectionDifferenceDerivative ``Submission.DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_sub_deTurckLieConnectionDifferenceDerivative

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_map_add_deTurckLieConnectionDifferenceDerivative (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (a + b) =
      cotangentToDual (I := I) (x := x) om a + cotangentToDual (I := I) (x := x) om b := by
  simp only [show ∀ v : TangentSpace I x, cotangentToDual (I := I) (x := x) om v =
      cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
  exact map_add _ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_add_deTurckLieConnectionDifferenceDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_add_deTurckLieConnectionDifferenceDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_add_deTurckLieConnectionDifferenceDerivative ``Submission.DifferentialGeometry.Analysis.Sobolev.cotangentToDual_map_add_deTurckLieConnectionDifferenceDerivative

private noncomputable def deTurckLieConnectionDifferenceDerivKernelCLM (g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0
      map_add' := fun v0 v0' => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [add_apply]
        exact deTurckLieConnectionDifferenceDerivativeCovKernel_add_left (I := I) g₁ g_bg x v0 v0' p q
      map_smul' := fun c v0 => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [RingHom.id_apply, smul_apply]
        exact deTurckLieConnectionDifferenceDerivativeCovKernel_smul_left (I := I) g₁ g_bg x c v0 p q }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivKernelCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivKernelCLM target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieConnectionDifferenceDerivativeCovKernelCLM_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x v0 p q =
      connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q := by
  rw [deTurckLieConnectionDifferenceDerivKernelCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovKernelCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovKernelCLM_apply target :: scope.openDecls } }

private noncomputable def deTurckLieConnectionDifferenceDerivativeLoweredCovec (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        g₀.inner x (deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3))
          (m 0)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true]
        · exact (g₀.inner x
            (deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x
              (m 1) (m 2) (m 3))).map_add a a'
        · rw [(deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x).map_add,
            add_apply, add_apply, (g₀.inner x).map_add, add_apply]
        · rw [(deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1)).map_add,
            add_apply, (g₀.inner x).map_add, add_apply]
        · rw [(deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2)).map_add,
            (g₀.inner x).map_add, add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true]
        · exact (g₀.inner x
            (deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x
              (m 1) (m 2) (m 3))).map_smul c a
        · rw [(deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x).map_smul,
            smul_apply, smul_apply, (g₀.inner x).map_smul, smul_apply]
        · rw [(deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1)).map_smul,
            smul_apply, (g₀.inner x).map_smul, smul_apply]
        · rw [(deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2)).map_smul,
            (g₀.inner x).map_smul, smul_apply]
      cont := by
        have hK : Continuous (fun m : Fin 4 → TangentSpace I x =>
            deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) :=
          (((deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x).continuous.comp
            (continuous_apply 1)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((g₀.inner x).continuous.comp hK).clm_apply (continuous_apply 0) }
    : Tensor0SSpace 4 I x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCovec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCovec target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] private lemma deTurckLieConnectionDifferenceDerivativeLoweredCovec_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    deTurckLieConnectionDifferenceDerivativeLoweredCovec (I := I) g₀ g₁ g_bg x m =
      g₀.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  change g₀.inner x (deTurckLieConnectionDifferenceDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3))
    (m 0) = _
  rw [deTurckLieConnectionDifferenceDerivativeCovKernelCLM_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCovec_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCovec_apply target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieConnectionDifferenceDerivativeLoweredScalar_global (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovariantDerivativeA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₀.inner x
        (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredScalar_global
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredScalar_global target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieConnectionDifferenceDerivativeLoweredScalar_contMDiffAt (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        g₀.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (V1 x) (V2 x) (V3 x)) (V0 x)) x₀ := by
  have hglob := deTurckLieConnectionDifferenceDerivativeLoweredScalar_global (I := I) (M := M) g₀ g₁ g_bg
    (V0 := fun b => V1 b) (W := fun b => V0 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V1.contMDiff V0.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredScalar_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredScalar_contMDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieConnectionDifferenceDerivativeLoweredCovec_section_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (deTurckLieConnectionDifferenceDerivativeLoweredCovec (I := I) g₀ g₁ g_bg x)) := by
  classical
  let _ := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (deTurckLieConnectionDifferenceDerivativeLoweredCovec (I := I) g₀ g₁ g_bg x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (Y (σ 1) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 0) x)) x₀ :=
    deTurckLieConnectionDifferenceDerivativeLoweredScalar_contMDiffAt (I := I) (M := M) g₀ g₁ g_bg
      (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ (b (σ k))
  change deTurckLieConnectionDifferenceDerivativeLoweredCovec (I := I) g₀ g₁ g_bg x (fun k => e₁.symmL ℝ x (b (σ k))) = _
  rw [deTurckLieConnectionDifferenceDerivativeLoweredCovec_apply]
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCovec_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCovec_section_contMDiff target :: scope.openDecls } }

private def deTurckLieConnectionDifferenceDerivativeLoweredField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => deTurckLieConnectionDifferenceDerivativeLoweredCovec (I := I) g₀ g₁ g_bg x,
    deTurckLieConnectionDifferenceDerivativeLoweredCovec_section_contMDiff (I := I) (M := M) g₀ g₁ g_bg⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredField target :: scope.openDecls } }

def deTurckLieConnectionDifferenceDerivativeLoweredCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (deTurckLieConnectionDifferenceDerivativeLoweredField (I := I) (M := M) g₀ g₁ g_bg)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (deTurckLieConnectionDifferenceDerivativeLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x =
      Tensor0SSpace.toModel (deTurckLieConnectionDifferenceDerivativeLoweredCovec (I := I) g₀ g₁ g_bg x) := by
  rw [unitModel]
  rw [show (deTurckLieConnectionDifferenceDerivativeLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (deTurckLieConnectionDifferenceDerivativeLoweredField (I := I) (M := M) g₀ g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4 (deTurckLieConnectionDifferenceDerivativeLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₀.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 3)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
  rw [deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeLoweredCc_unitModel_apply

def deTurckLieConnectionDifferenceDerivativeConnTermPt (g₀ gc : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connectionDifference (I := I) gc g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connectionDifference (I := I) gc g₀ x)
      (fun V0 W => PDE.DeTurck.connectionDifference_contMDiff (I := I) gc g₀ V0.contMDiff W.contMDiff)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeConnTermPt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeConnTermPt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeConnTermPt ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeConnTermPt

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieConnectionDifferenceDerivativeConnTermPt_apply (g₀ gc : SmoothRiemannianMetric I M) (x : M) :
    deTurckLieConnectionDifferenceDerivativeConnTermPt (I := I) (M := M) g₀ gc x = PDE.DeTurck.connectionDifference (I := I) gc g₀ x := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeConnTermPt_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeConnTermPt_apply target :: scope.openDecls } }

def deTurckLieConnectionDifferenceDerivativeQuadCc (g₀ g_arm g_out : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
    (termSlotEndoPassZeroCc (I := I) (M := M) g₀ (deTurckLieConnectionDifferenceDerivativeConnTermPt (I := I) (M := M) g₀ g_arm))
    (connectionDifferenceSection (I := I) g_out g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma deTurckLieConnectionDifferenceDerivativeQuadCc_toModel (g₀ g_arm g_out : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g_arm g_out).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connectionDifference (I := I) g_out g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g_arm g₀ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 1))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2)))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))) := by
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g_arm g_out).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
          (termSlotEndoPassZeroCc (I := I) (M := M) g₀
            (deTurckLieConnectionDifferenceDerivativeConnTermPt (I := I) (M := M) g₀ g_arm))
          (connectionDifferenceSection (I := I) g_out g₀)).toSection x) om) from rfl]
  rw [toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval (I := I) (M := M) g₀
    (deTurckLieConnectionDifferenceDerivativeConnTermPt (I := I) (M := M) g₀ g_arm) (connectionDifferenceSection (I := I) g_out g₀) x om w]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connectionDifferenceSection (I := I) g_out g₀).toSection x) om) =
      connectionDifferencePairing (I := I) g_out g₀ x om from rfl]
  rw [Tensor0SSpace.toModel_apply_model_vector]
  rw [show (fun j : Fin 2 =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (if j = 0 then
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (deTurckLieConnectionDifferenceDerivativeConnTermPt (I := I) (M := M) g₀ g_arm x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 1))
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2)))
          else w 0)) =
      (Fin.cons (PDE.DeTurck.connectionDifference (I := I) g_arm g₀ x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 1))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2)))
        (fun _ : Fin 1 =>
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0)) :
        Fin 2 → TangentSpace I x) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [if_pos rfl, ContinuousLinearEquiv.symm_apply_apply]
      rfl
    · intro i
      rw [if_neg (Fin.succ_ne_zero i)]
      rfl]
  rw [connectionDifferencePairing_apply]
  rw [cotangentToDual_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc_toModel ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeQuadCc_toModel

def deTurckLieConnectionDifferenceDerivativeKernelRaisedCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)
    - covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g_bg g₀)
    + deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g₁ g₁
    - deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g_bg g₁
    - rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2)
        (deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g₁ g₁)
    + rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2)
        (deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g₁ g_bg)
    - rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
        (deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g₁ g₁)
    + rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
        (deTurckLieConnectionDifferenceDerivativeQuadCc (I := I) (M := M) g₀ g₁ g_bg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeKernelRaisedCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeKernelRaisedCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeKernelRaisedCc ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeKernelRaisedCc

def deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
  letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  ⟨fun b : M => g0FlatCLM (I := I) g₀ b
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b),
   by
     have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
         (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
           (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b)) :=
       smoothExtensionTangent_contMDiff (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)
     exact ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) hU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
lemma deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection (I := I) (M := M) g₀ x om x = om := by
  change g0FlatCLM (I := I) g₀ x
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) x) = om
  rw [smoothExtensionTangent_eq (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)]
  exact g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection_self ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovectorExtensionSection_self

end DeTurckLieConnectionDifferenceDerivativeGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
