import Submission.DifferentialGeometry.Geometry.Metric.Conformal
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import Mathlib.Analysis.Calculus.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.InnerProductSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local instance _root_.Submission.DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry ``Submission.DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry ``Submission.DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 ``Submission.DifferentialGeometry.Geometry.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1
local instance _root_.Submission.DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 ``Submission.DifferentialGeometry.Geometry.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1


def conformalEuclideanMetric (f : V → ℝ) (hf : ContDiff ℝ ∞ f) :
    SmoothRiemannianMetric 𝓘(ℝ, V) V :=
  conformalMetric (euclideanMetric V) f hf.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.conformalEuclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.conformalEuclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.conformalEuclideanMetric ``Submission.DifferentialGeometry.Geometry.conformalEuclideanMetric

@[simp] theorem conformalEuclideanMetric_inner (f : V → ℝ)
    (hf : ContDiff ℝ ∞ f) (x v w : V) :
    (conformalEuclideanMetric f hf).inner x v w =
      Real.exp (2 * f x) * _root_.Inner.inner ℝ v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.conformalEuclideanMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.conformalEuclideanMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.conformalEuclideanMetric_inner ``Submission.DifferentialGeometry.Geometry.conformalEuclideanMetric_inner

private theorem conformal_bilinear_hasFDerivAt {f : V → ℝ} {z : V}
    (hf : DifferentiableAt ℝ f z) :
    HasFDerivAt (fun y => Real.exp (2 * f y) • (innerSL ℝ (E := V)))
      ((Real.exp (2 * f z) • ((2 : ℝ) • fderiv ℝ f z)).smulRight (innerSL ℝ)) z := by
  exact ((hf.hasFDerivAt.const_mul 2).exp).smul_const (innerSL ℝ (E := V))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.conformal_bilinear_hasFDerivAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.conformal_bilinear_hasFDerivAt target :: scope.openDecls } }

private theorem conformal_bilinear_coercive (f : V → ℝ) (z : V) :
    IsCoercive (Real.exp (2 * f z) • (innerSL ℝ (E := V))) := by
  refine ⟨Real.exp (2 * f z), Real.exp_pos _, ?_⟩
  intro v
  change Real.exp (2 * f z) * ‖v‖ * ‖v‖ ≤ Real.exp (2 * f z) * _root_.Inner.inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.conformal_bilinear_coercive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.conformal_bilinear_coercive target :: scope.openDecls } }

variable [FiniteDimensional ℝ V]


def conformalEuclideanCorrection (f : V → ℝ) (z v w : V) : V :=
  fderiv ℝ f z v • w + fderiv ℝ f z w • v - _root_.Inner.inner ℝ v w • gradient f z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.conformalEuclideanCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.conformalEuclideanCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.conformalEuclideanCorrection ``Submission.DifferentialGeometry.Geometry.conformalEuclideanCorrection

private theorem conformal_koszulVec {f : V → ℝ} {z : V}
    (hf : DifferentiableAt ℝ f z) (v w : V) :
    MetricKoszul.koszulVec (conformal_bilinear_coercive f z)
      (fderiv ℝ (fun y => Real.exp (2 * f y) • (innerSL ℝ (E := V))) z) v w =
      conformalEuclideanCorrection f z v w := by
  apply (conformal_bilinear_coercive f z).bilin_injective
  rw [MetricKoszul.koszulVec, IsCoercive.apply_sharp]
  ext u
  rw [MetricKoszul.koszul_cov_apply, (conformal_bilinear_hasFDerivAt hf).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  change (1 / 2 : ℝ) *
      (Real.exp (2 * f z) * (2 * fderiv ℝ f z v) * _root_.Inner.inner ℝ w u +
       Real.exp (2 * f z) * (2 * fderiv ℝ f z w) * _root_.Inner.inner ℝ v u -
       Real.exp (2 * f z) * (2 * fderiv ℝ f z u) * _root_.Inner.inner ℝ v w) =
    Real.exp (2 * f z) * _root_.Inner.inner ℝ (conformalEuclideanCorrection f z v w) u
  simp only [conformalEuclideanCorrection, inner_sub_left,
    inner_add_left, real_inner_smul_left, inner_gradient_left]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.conformal_koszulVec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.conformal_koszulVec target :: scope.openDecls } }




theorem leviCivita_conformalEuclidean {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    {Y : V → V} {z : V} (hY : DifferentiableAt ℝ Y z) (v : V) :
    LeviCivita (conformalEuclideanMetric f hf) Y z v =
      fderiv ℝ Y z v + conformalEuclideanCorrection f z v (Y z) := by
  let B : V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun y => Real.exp (2 * f y) • innerSL ℝ
  have hB : (fun y => tangentBilinearFormToModel y
      ((conformalEuclideanMetric f hf).inner y)) = B := by
    funext y
    ext u w
    rfl
  have hYs : MDifferentiableAt 𝓘(ℝ, V) (𝓘(ℝ, V).prod 𝓘(ℝ, V))
      (fun y => (⟨y, Y y⟩ : TangentBundle 𝓘(ℝ, V) V)) z := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_id, ?_⟩
    convert! hY.mdifferentiableAt with y
    simp
  have h := cov_eq_fderiv_add (conformalEuclideanMetric f hf) B
    (Filter.EventuallyEq.of_eq hB)
    (conformal_bilinear_hasFDerivAt (hf.differentiable (by simp) z)).differentiableAt
    (conformal_bilinear_coercive f z) Y hYs v
  change LeviCivita (conformalEuclideanMetric f hf) Y z v = _ at h
  rw [conformal_koszulVec (hf.differentiable (by simp) z)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leviCivita_conformalEuclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leviCivita_conformalEuclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leviCivita_conformalEuclidean ``Submission.DifferentialGeometry.Geometry.leviCivita_conformalEuclidean

end DifferentialGeometry.Geometry
