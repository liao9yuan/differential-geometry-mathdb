import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.ParallelNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma covGrad_contMDiff_totalSpaceMk
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 3 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 3 ℝ E)
        (E := fun z : M => TensorRSSpace 0 3 I z) b
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection b)) :=
  (covGrad (I := I) (M := M) g 0 2 T₀).toSection.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma rawTensorConnLap_covGrad_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    rawTensorConnLap (I := I) g 0 3
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 3
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x :=
  rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 3
    (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_eq_frame_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_eq_frame_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_eq_frame_trace ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_covGrad_eq_frame_trace

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma covGrad_apply_unit_eval_two
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 S x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0)))
          (unitZeroSec (I := I) (M := M) x))
        (Matrix.vecTail v) := by
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (covGrad (I := I) (M := M) g 0 2 S).toSection x)
        (unitZeroSec (I := I) (M := M) x))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0)))
        (unitZeroSec (I := I) (M := M) x))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (Matrix.vecTail v i))
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 2 S x
    (unitZeroSec (I := I) (M := M) x)
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval_two ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval_two

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma covGrad_apply_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s S x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0)))
          (unitZeroSec (I := I) (M := M) x))
        (Matrix.vecTail v) := by
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s S).toSection x)
        (unitZeroSec (I := I) (M := M) x))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0)))
        (unitZeroSec (I := I) (M := M) x))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (Matrix.vecTail v i))
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 s S x
    (unitZeroSec (I := I) (M := M) x)
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_apply_unit_eval

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma curry_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x w))
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x).injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.eval
      (tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w) m =
    Tensor0SSpace.eval
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x w))
        (unitZeroSec (I := I) (M := M) x)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval]
  rw [covGrad_apply_unit_eval (I := I) (M := M) g s S x (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval ``Submission.DifferentialGeometry.Geometry.Curvature.curry_covGrad_unit_eval

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDeriv_unit_eval_eq_three
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_three ``Submission.DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq_three

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDeriv_unit_eval_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq ``Submission.DifferentialGeometry.Geometry.Curvature.covDeriv_unit_eval_eq

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covApply_unit_eval_eq_three
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        covApply (tensorCov (I := I) g 0 3) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq_three (I := I) (M := M) g σ y (X y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq_three ``Submission.DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq_three

noncomputable def covApplyCovGradSection
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M =>
      covApply (tensorCov (I := I) g 0 3) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 3
      (covGrad_contMDiff_totalSpaceMk (I := I) (M := M) g T₀) hX)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection ``Submission.DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma covApplyCovGradSection_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyCovGradSection (I := I) (M := M) g T₀ hX y =
      covApply (tensorCov (I := I) g 0 3) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection_apply ``Submission.DifferentialGeometry.Geometry.Curvature.covApplyCovGradSection_apply

noncomputable def unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    Π y : M, Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
      (unitZeroSec (I := I) (M := M) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.unitGradField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.unitGradField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.unitGradField ``Submission.DifferentialGeometry.Geometry.Curvature.unitGradField

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma unitGradField_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (y : M) :
    unitGradField (I := I) (M := M) g T₀ y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.unitGradField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.unitGradField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.unitGradField_apply ``Submission.DifferentialGeometry.Geometry.Curvature.unitGradField_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma tensorSecondCovDeriv_covGrad_unit_eval_two
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorSecondCovDeriv (I := I) g 0 3 B B
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) B
            (unitGradField (I := I) (M := M) g T₀)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [sub_apply]
  congr 1
  · have hσ : (fun y : M => covApplyCovGradSection (I := I) (M := M) g T₀ hB y) =
        (fun y : M => covApply (tensorCov (I := I) g 0 3) B
          (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y) := by
      funext y; exact covApplyCovGradSection_apply (I := I) (M := M) g T₀ hB y
    have h1 := covDeriv_unit_eval_eq_three (I := I) (M := M) g
      (covApplyCovGradSection (I := I) (M := M) g T₀ hB) x (B x)
    simp only [covApplyCovGradSection_apply] at h1
    rw [h1]
    rw [covApply_unit_eval_eq_three (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection B]
    rfl
  · exact covDeriv_unit_eval_eq_three (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection x ((LeviCivita (I := I) g).toFun B x (B x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval_two ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval_two

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π y : M, Tensor0SSpace (s + 1) I y)
    {Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M W y)) x)
    (hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x)
    (hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0SCurry (I := I) (M := M) s x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          W x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x (Vfield x) -
        Tensor0SNabla.curriedSection I M W x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (E_U := E) (U := TangentSpace I) (F := Tensor0SModel s ℝ E)
    (V := fun z : M => Tensor0SSpace s I z)
    (cov_U := LeviCivita (I := I) g)
    (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (τ := Tensor0SNabla.curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0SCurry (I := I) (M := M) s x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        W x (Vfield x)) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M) (E_U := E) (U := TangentSpace I)
        (F := Tensor0SModel s ℝ E)
        (V := fun z : M => Tensor0SSpace s I z)
        (cov_U := LeviCivita (I := I) g)
        (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (τ := Tensor0SNabla.curriedSection I M W) x (Vfield x) := by
    rw [show
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          W x (Vfield x) =
        (Tensor0SNabla.tensor0SCovariantDerivativeSucc I M (LeviCivita (I := I) g)
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))).toFun
          W x (Vfield x) from by
      rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_eq]]
    rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_apply]
    exact (tensor0SCurry (I := I) (M := M) s x).apply_symm_apply _
  rw [hsucc]
  exact hHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection ``Submission.DifferentialGeometry.Geometry.Curvature.curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection

noncomputable def unitGradFieldCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    Π y : M, Tensor0SSpace (s + 1) I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      (covGrad (I := I) (M := M) g 0 s S).toSection y)
      (unitZeroSec (I := I) (M := M) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma unitGradFieldCovariantTensor_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (y : M) :
    unitGradFieldCovariantTensor (I := I) (M := M) g s S y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        (covGrad (I := I) (M := M) g 0 s S).toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor_apply ``Submission.DifferentialGeometry.Geometry.Curvature.unitGradFieldCovariantTensor_apply

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma contMDiff_unitGradFieldCovariantTensor (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        (unitGradFieldCovariantTensor (I := I) (M := M) g s S y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (s + 1) I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (covGrad (I := I) (M := M) g 0 s S).toSection y))) :=
    (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace (s + 1) I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel (s + 1) ℝ E) hϕ hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradFieldCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradFieldCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradFieldCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.contMDiff_unitGradFieldCovariantTensor

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma contMDiff_curried_unitGradFieldCovariantTensor (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M (unitGradFieldCovariantTensor (I := I) (M := M) g s S) y)) :=
  (Tensor0SNabla.contMDiff_curriedSection_iff_section (I := I) (M := M)
    (unitGradFieldCovariantTensor (I := I) (M := M) g s S)).mp
    (contMDiff_unitGradFieldCovariantTensor (I := I) (M := M) g s S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradFieldCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradFieldCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradFieldCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.contMDiff_curried_unitGradFieldCovariantTensor

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma curry_unitGradFieldCovariantTensor_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (y : M) (w : TangentSpace I y) :
    Tensor0SNabla.curriedSection I M (unitGradFieldCovariantTensor (I := I) (M := M) g s S) y w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        tensorCovDerivAt (I := I) (M := M) g 0 s S y
          (tangentSpaceModelContinuousLinearEquiv (I := I) y w))
        (unitZeroSec (I := I) (M := M) y) := by
  rw [Tensor0SNabla.curriedSection_apply, unitGradFieldCovariantTensor_apply]
  exact curry_covGrad_unit_eval (I := I) (M := M) g s S y w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curry_unitGradFieldCovariantTensor_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curry_unitGradFieldCovariantTensor_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curry_unitGradFieldCovariantTensor_eq ``Submission.DifferentialGeometry.Geometry.Curvature.curry_unitGradFieldCovariantTensor_eq

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma covGrad_contMDiff_totalSpaceMk_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b
        ((covGrad (I := I) (M := M) g 0 s S).toSection b)) :=
  (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_contMDiff_totalSpaceMk_covariantTensor

noncomputable def covApplyCovGradSectionCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    @ContMDiffSection ℝ _ E _ _ H _ I M _ _ (TensorRSModel 0 (s + 1) ℝ E) _ _ ∞
      (fun y : M => TensorRSSpace 0 (s + 1) I y)
      (Tensor0SBundle.tensorRSBundleTopology 0 (s + 1)) (fun _ => inferInstance)
      (Tensor0SBundle.tensorRSBundleFiber 0 (s + 1)) :=
  @ContMDiffSection.mk ℝ _ E _ _ H _ I M _ _ (TensorRSModel 0 (s + 1) ℝ E) _ _ ∞
    (fun y : M => TensorRSSpace 0 (s + 1) I y)
    (Tensor0SBundle.tensorRSBundleTopology 0 (s + 1)) (fun _ => inferInstance)
    (Tensor0SBundle.tensorRSBundleFiber 0 (s + 1))
    (fun y : M =>
      covApply (tensorCov (I := I) g 0 (s + 1)) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 (s + 1)
      (covGrad_contMDiff_totalSpaceMk_covariantTensor (I := I) (M := M) g s S) hX)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma covApplyCovGradSectionCovariantTensor_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyCovGradSectionCovariantTensor (I := I) (M := M) g s S hX y =
      covApply (tensorCov (I := I) g 0 (s + 1)) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor_apply ``Submission.DifferentialGeometry.Geometry.Curvature.covApplyCovGradSectionCovariantTensor_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covApply_unit_eval_eq
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from
        covApply (tensorCov (I := I) g 0 t) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq (I := I) (M := M) g t σ y (X y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq ``Submission.DifferentialGeometry.Geometry.Curvature.covApply_unit_eval_eq

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma tensorSecondCovDeriv_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) B B
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
              (LeviCivita (I := I) g)) B
            (unitGradFieldCovariantTensor (I := I) (M := M) g s S)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (unitGradFieldCovariantTensor (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [sub_apply]
  congr 1
  · have h1 := covDeriv_unit_eval_eq (I := I) (M := M) g (s + 1)
      (covApplyCovGradSectionCovariantTensor (I := I) (M := M) g s S hB) x (B x)
    simp only [covApplyCovGradSectionCovariantTensor_apply] at h1
    rw [h1]
    rw [covApply_unit_eval_eq (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection B]
    rfl
  · exact covDeriv_unit_eval_eq (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection x ((LeviCivita (I := I) g).toFun B x (B x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_covGrad_unit_eval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) m)) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g 0 s X Y (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x))
        m := by
  classical
  set GS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hGS
  rw [covGrad_apply_unit_eval (I := I) (M := M) g (s + 1) GS x
    (Fin.cons (X x) (Fin.cons (Y x) m))]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons (X x) (Fin.cons (Y x) m) ∘ Fin.succ) = Fin.cons (Y x) m from
    funext (fun j => by simp [Fin.cons_succ])]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (s + 1) GS x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x)))
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldCovariantTensor (I := I) (M := M) g s S) x (X x) from by
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 (s + 1) GS x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x)),
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply]
    exact covDeriv_unit_eval_eq (I := I) (M := M) g (s + 1) GS.toSection x (X x)]
  rw [show Tensor0SSpace.eval
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (unitGradFieldCovariantTensor (I := I) (M := M) g s S) x (X x))
        (Fin.cons (Y x) m) =
      Tensor0SSpace.eval
        (tensor0SCurry (I := I) (M := M) s x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
            (unitGradFieldCovariantTensor (I := I) (M := M) g s S) x (X x)) (Y x)) m from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldCovariantTensor (I := I) (M := M) g s S) x (X x)) (v0 := Y x) (vs := m)).symm]
  rw [curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g s
    (unitGradFieldCovariantTensor (I := I) (M := M) g s S) (Vfield := X) (Y := Y) (x := x)
    ((contMDiff_curried_unitGradFieldCovariantTensor (I := I) (M := M) g s S x).mdifferentiableAt (by simp))
    ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M
        (unitGradFieldCovariantTensor (I := I) (M := M) g s S) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          tensorCovDerivAt (I := I) (M := M) g 0 s S y
            (tangentSpaceModelContinuousLinearEquiv (I := I) y (Y y)))
          (unitZeroSec (I := I) (M := M) y)) from
    funext (fun y => curry_unitGradFieldCovariantTensor_eq (I := I) (M := M) g s S y (Y y))]
  rw [curry_unitGradFieldCovariantTensor_eq (I := I) (M := M) g s S x
    ((LeviCivita (I := I) g).toFun Y x (X x))]
  rw [tensorSecondCovDeriv_def (I := I) g 0 s X Y (fun y : M => S.toSection y) x]
  refine congrArg (fun T : Tensor0SSpace s I x => Tensor0SSpace.eval T m) ?_
  rw [sub_apply]
  have houter :
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
              tensorCovDerivAt (I := I) (M := M) g 0 s S y
                (tangentSpaceModelContinuousLinearEquiv (I := I) y (Y y)))
              (unitZeroSec (I := I) (M := M) y)) x (X x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) Y (fun y : M => S.toSection y)) x (X x))
          (unitZeroSec (I := I) (M := M) x) := by
    set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
      ContMDiffSection.mk
        (fun y : M => covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y)
        (covApplyRS_contMDiff (I := I) g 0 s
          (T := fun z : M => S.toSection z) S.toSection.contMDiff (X := Y) hY) with hσ
    have hσapp : ∀ y : M, σ y =
        covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y := fun y => rfl
    rw [show (covApply (tensorCov (I := I) g 0 s) Y (fun y : M => S.toSection y)) =
        (fun y : M => σ y) from funext (fun y => (hσapp y).symm)]
    rw [covDeriv_unit_eval_eq (I := I) (M := M) g s σ x (X x)]
    refine congrArg (fun F : Π z : M, Tensor0SSpace s I z =>
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun F x (X x)) ?_
    funext y
    rw [hσapp y, covApply_apply, tensorCovDerivAt_def (I := I) (M := M) g 0 s S y
      (tangentSpaceModelContinuousLinearEquiv (I := I) y (Y y))]
    rw [(tangentSpaceModelContinuousLinearEquiv (I := I) y).symm_apply_apply]
  have hchr :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((LeviCivita (I := I) g).toFun Y x (X x))))
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s S x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((LeviCivita (I := I) g).toFun Y x (X x))),
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply]
  rw [houter, hchr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval

end Curvature
end Geometry
end DifferentialGeometry

end
