import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Weitzenbock.IntegratedSecondOrder
import Submission.DifferentialGeometry.Geometry.Curvature.SecondOrderDefect.GradientSlotLeibniz
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorThirdOrder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def pointwiseTensorCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv

omit [CompactSpace M] in
theorem pointwiseTensorCurv_commutator_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) =
      covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S)
        + pointwiseTensorCurv (I := I) (M := M) g s S := by
  set A : SmoothCcTensor g 0 (s + 1) :=
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) with hA
  set B : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) with hB
  change A = B + (A - B)
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_commutator_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_commutator_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_commutator_eq ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_commutator_eq

omit [CompactSpace M] in
theorem pointwiseTensorCurv_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x := by
  have hdef : (pointwiseTensorCurv (I := I) (M := M) g s S) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) := rfl
  rw [hdef, SmoothCcTensor.toSection_sub]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_sub ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_sub

omit [CompactSpace M] in
theorem rawTensorConnLap_gradTensor_toSection_eq_frame_trace_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 (s + 1)
    (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace_covariantTensor

omit [CompactSpace M] in
theorem covGrad_rawConnLap_toSection_eq_frame_sum_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) 0 s x
          ((tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => S.toSection z) y) x) := by
  have hS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 s S).toSection y) =
      (fun y : M => rawTensorConnLap (I := I) g 0 s (fun z : M => S.toSection z) y) from by
    funext y; rw [rawTensorConnLapSmooth_toSection_apply]]
  exact covGradBundleEquiv_covDeriv_rawConnLap_eq_sum (I := I) g 0 s hS x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_toSection_eq_frame_sum_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_toSection_eq_frame_sum_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_toSection_eq_frame_sum_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_toSection_eq_frame_sum_covariantTensor

omit [CompactSpace M] in
theorem pointwiseTensorCurv_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x)) := by
  classical
  rw [pointwiseTensorCurv_toSection_eq_sub (I := I) (M := M) g s S x]
  rw [rawTensorConnLap_gradTensor_toSection_eq_frame_trace_covariantTensor (I := I) (M := M) g s S x]
  rw [covGrad_rawConnLap_toSection_eq_frame_sum_covariantTensor (I := I) (M := M) g s S x]
  rw [← Finset.sum_sub_distrib]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_frame_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_frame_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_frame_sum ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_frame_sum

noncomputable def pointwiseTensorCurvPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) : ℝ :=
  tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x))
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((covGrad (I := I) (M := M) g 0 s S).toSection x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing

omit [CompactSpace M] in
lemma pointwiseTensorCurvPairing_eq_toFun
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    pointwiseTensorCurvPairing (I := I) (M := M) g s S x =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing_eq_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing_eq_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing_eq_toFun ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurvPairing_eq_toFun

omit [CompactSpace M] in
theorem abs_pointwiseTensorCurvPairing_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    |pointwiseTensorCurvPairing (I := I) (M := M) g s S x| ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by
  classical
  rw [pointwiseTensorCurvPairing]
  have hcs := abs_tensorInnerPointwise_le_mul (I := I) (M := M) g 0 (s + 1) x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x))
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((covGrad (I := I) (M := M) g 0 s S).toSection x))
  rw [tensorPointwiseNorm, tensorPointwiseNorm,
    ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x),
    ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x)] at hcs
  exact hcs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.abs_pointwiseTensorCurvPairing_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.abs_pointwiseTensorCurvPairing_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.abs_pointwiseTensorCurvPairing_le ``Submission.DifferentialGeometry.Geometry.Curvature.abs_pointwiseTensorCurvPairing_le

omit [CompactSpace M] in
theorem pointwiseTensorCurv_pairing_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (K_R K_dR : ℝ)
    (hfibre :
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
        K_R * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
          K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (S.toSection x))) :
    |pointwiseTensorCurvPairing (I := I) (M := M) g s S x| ≤
      K_R * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) *
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by
  classical
  set sqCurv : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) with hsqCurv
  set sqGrad : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x)) with hsqGrad
  set sqS : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))
    with hsqS
  have hsqGrad_nn : 0 ≤ sqGrad := Real.sqrt_nonneg _
  have hgrad_sq : sqGrad * sqGrad =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    rw [hsqGrad]
    exact Real.mul_self_sqrt
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  have hcs := abs_pointwiseTensorCurvPairing_le (I := I) (M := M) g s S x
  rw [← hsqCurv, ← hsqGrad] at hcs
  calc |pointwiseTensorCurvPairing (I := I) (M := M) g s S x|
      ≤ sqCurv * sqGrad := hcs
    _ ≤ (K_R * sqGrad + K_dR * sqS) * sqGrad :=
        mul_le_mul_of_nonneg_right hfibre hsqGrad_nn
    _ = K_R * (sqGrad * sqGrad) + K_dR * sqS * sqGrad := by ring
    _ = K_R * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
          K_dR * sqS * sqGrad := by rw [hgrad_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_pairing_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_pairing_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_pairing_bound ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_pairing_bound

noncomputable def tensor3rdCurvGenuine
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor3rdCurvGenuine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor3rdCurvGenuine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor3rdCurvGenuine ``Submission.DifferentialGeometry.Geometry.Curvature.tensor3rdCurvGenuine

noncomputable def tensor3rdCurvBracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
        (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
      + (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
          (smoothOrthoFrame (I := I) g x i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor3rdCurvBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor3rdCurvBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor3rdCurvBracket ``Submission.DifferentialGeometry.Geometry.Curvature.tensor3rdCurvBracket

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem Tensor3rdCurv_eq_genuine_add_bracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorThirdOrderCurvatureDefect (I := I) g r s W T x =
      tensor3rdCurvGenuine (I := I) g r s W T x +
        tensor3rdCurvBracket (I := I) g r s W T x := by
  classical
  rw [Tensor3rdCurv_def, tensor3rdCurvGenuine, tensor3rdCurvBracket,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor3rdCurv_eq_genuine_add_bracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor3rdCurv_eq_genuine_add_bracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor3rdCurv_eq_genuine_add_bracket ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor3rdCurv_eq_genuine_add_bracket

omit [CompactSpace M] [I.Boundaryless] in
theorem frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g r s) W T)) x
            (smoothOrthoFrame (I := I) g x i x)) -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g r s).toFun
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T)) x
              (W x)) =
      tensor3rdCurvGenuine (I := I) g r s W T x +
        tensor3rdCurvBracket (I := I) g r s W T x := by
  rw [frame_trace_thirdCovDeriv_swap (I := I) g r s hW hT,
    Tensor3rdCurv_eq_genuine_add_bracket (I := I) g r s W T x]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket ``Submission.DifferentialGeometry.Geometry.Curvature.frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_tensor3rdCurvGenuine_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M)
    (cR cdR : ℝ)
    (hR : ∀ i : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x) ≤ cR)
    (hdR : ∀ i : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          ((tensorCov (I := I) g r s).toFun
            (fun b : M => riemannSec (tensorCov (I := I) g r s)
              (smoothOrthoFrame (I := I) g x i) W T b) x
            (smoothOrthoFrame (I := I) g x i x)) ≤ cdR) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (tensor3rdCurvGenuine (I := I) g r s W T x) ≤
      (2 * (Module.finrank ℝ E : ℝ)) * (Module.finrank ℝ E : ℝ) * (cR + cdR) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set F : Fin n → TensorRSSpace r s I x := fun i =>
    riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x) with hF
  have hsum : tensor3rdCurvGenuine (I := I) g r s W T x = ∑ i : Fin n, F i := rfl
  rw [hsum]
  have hcard := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r s x
    (Finset.univ : Finset (Fin n)) F
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hper : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (F i) ≤ 2 * (cR + cdR) := by
    intro i
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x
      (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x)
      ((tensorCov (I := I) g r s).toFun
        (fun b : M => riemannSec (tensorCov (I := I) g r s)
          (smoothOrthoFrame (I := I) g x i) W T b) x
        (smoothOrthoFrame (I := I) g x i x))
    have h1 := hR i
    have h2 := hdR i
    calc riemannianFiberNormSq (I := I) (M := M) g r s x (F i)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x
              (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
                (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g r s x
              ((tensorCov (I := I) g r s).toFun
                (fun b : M => riemannSec (tensorCov (I := I) g r s)
                  (smoothOrthoFrame (I := I) g x i) W T b) x
                (smoothOrthoFrame (I := I) g x i x)) := hadd
      _ ≤ 2 * cR + 2 * cdR := by
            have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
            have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
            linarith
      _ = 2 * (cR + cdR) := by ring
  have hsum_le : ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i) ≤
      (n : ℝ) * (2 * (cR + cdR)) := by
    calc ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i)
        ≤ ∑ _i : Fin n, (2 * (cR + cdR)) := Finset.sum_le_sum (fun i _ => hper i)
      _ = (n : ℝ) * (2 * (cR + cdR)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (∑ i : Fin n, F i)
      ≤ (n : ℝ) * ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i) := hcard
    _ ≤ (n : ℝ) * ((n : ℝ) * (2 * (cR + cdR))) :=
        mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = (2 * (n : ℝ)) * (n : ℝ) * (cR + cdR) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannianFiberNormSq_tensor3rdCurvGenuine_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannianFiberNormSq_tensor3rdCurvGenuine_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannianFiberNormSq_tensor3rdCurvGenuine_le ``Submission.DifferentialGeometry.Geometry.Curvature.riemannianFiberNormSq_tensor3rdCurvGenuine_le

omit [CompactSpace M] [I.Boundaryless] in
theorem tensor3rdCurv_pure_R_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (i : Fin (Module.finrank ℝ E))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x =
      riemannOp (tensorCov (I := I) g r s) x
        (smoothOrthoFrame (I := I) g x i x) (W x)
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T x) := by
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T b)) :=
    covApplyRS_contMDiff (I := I) g r s hT hB
  exact riemannSec_eq_riemannOp_tensorCov (I := I) g r s hB hW hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor3rdCurv_pure_R_eq_riemannOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor3rdCurv_pure_R_eq_riemannOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor3rdCurv_pure_R_eq_riemannOp ``Submission.DifferentialGeometry.Geometry.Curvature.tensor3rdCurv_pure_R_eq_riemannOp

end Curvature
end Geometry
end DifferentialGeometry

end
