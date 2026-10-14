import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.LocalLift
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import Submission.DifferentialGeometry.Geometry.Metric.AddCircle
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.DimensionOne
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
theorem LeviCivita_parameterTangent
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) (v : TangentSpace 𝓘(ℝ, ℝ) z) :
    (LeviCivita g).toFun parameterTangent z v =
      ((show ℝ from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun y => g.inner y (parameterTangent y) (parameterTangent y)) z v) /
          (2 * g.inner z (parameterTangent z) (parameterTangent z))) •
            parameterTangent z := by
  exact (LeviCivita_isMetricCompatible g).covariantDerivative_eq_smul_of_finrank_eq_one
    (Module.finrank_self ℝ)
    (contMDiff_parameterTangent.mdifferentiableAt (by decide))
    (parameterTangent_ne_zero z) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.LeviCivita_parameterTangent then
    throwError "Refusing to shadow existing declaration AddCircle.LeviCivita_parameterTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.LeviCivita_parameterTangent ``Submission.AddCircle.LeviCivita_parameterTangent

open _root_.AddCircle in
theorem LeviCivita_parameterTangent_eq_zero (z : AddCircle (1 : ℝ))
    (v : TangentSpace 𝓘(ℝ, ℝ) z) :
    (LeviCivita flatMetric).toFun parameterTangent z v = 0 := by
  rw [LeviCivita_parameterTangent]
  have heq : (fun y => flatMetric.inner y (parameterTangent y) (parameterTangent y)) =
      fun _ => (1 : ℝ) := funext flatMetric_parameterTangent_unit
  rw [heq, mfderiv_const]
  change ((0 : ℝ) / _) • parameterTangent z = 0
  rw [zero_div, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.LeviCivita_parameterTangent_eq_zero then
    throwError "Refusing to shadow existing declaration AddCircle.LeviCivita_parameterTangent_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.LeviCivita_parameterTangent_eq_zero ``Submission.AddCircle.LeviCivita_parameterTangent_eq_zero

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open _root_.AddCircle in
theorem covDerivAlong_parameterTangent_eq_zero {γ : ℝ → AddCircle (1 : ℝ)} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ t) :
    covDerivAlong flatMetric γ (fun s => parameterTangent (γ s)) t = 0 := by
  rw [← derivAlongWithin_leviCivita_eq_covDerivAlong flatMetric γ _
    (J := Set.univ) (by simp) hγ BoundarylessManifold.isInteriorPoint]
  rw [(LeviCivita flatMetric).derivAlongWithin_section hγ.mdifferentiableWithinAt
    (contMDiff_parameterTangent.mdifferentiableAt (by decide))]
  exact LeviCivita_parameterTangent_eq_zero _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.covDerivAlong_parameterTangent_eq_zero then
    throwError "Refusing to shadow existing declaration AddCircle.covDerivAlong_parameterTangent_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.covDerivAlong_parameterTangent_eq_zero ``Submission.AddCircle.covDerivAlong_parameterTangent_eq_zero

open _root_.AddCircle in
theorem covDerivAlong_coe_parameterTangent_eq_zero (t : ℝ) :
    covDerivAlong flatMetric (fun s : ℝ => (s : AddCircle (1 : ℝ)))
      (fun s => parameterTangent (s : AddCircle (1 : ℝ))) t = 0 :=
  covDerivAlong_parameterTangent_eq_zero (contMDiff_coe.mdifferentiableAt (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.covDerivAlong_coe_parameterTangent_eq_zero then
    throwError "Refusing to shadow existing declaration AddCircle.covDerivAlong_coe_parameterTangent_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.covDerivAlong_coe_parameterTangent_eq_zero ``Submission.AddCircle.covDerivAlong_coe_parameterTangent_eq_zero


open _root_.AddCircle in
theorem covDerivAlong_curveVelocity_of_local_lift
    {γ : ℝ → AddCircle (1 : ℝ)} {θ : ℝ → ℝ} {x : ℝ}
    (hθ : ContDiffAt ℝ 2 θ x)
    (heq : (fun y => (θ y : AddCircle (1 : ℝ))) =ᶠ[𝓝 x] γ) :
    covDerivAlong flatMetric γ
      (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ y (1 : ℝ)) x =
      deriv (deriv θ) x • parameterTangent (γ x) := by
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ x :=
    ((contMDiff_coe.mdifferentiableAt (by decide)).comp x
      (hθ.differentiableAt (by norm_num)).mdifferentiableAt).congr_of_eventuallyEq heq.symm
  have hV : DifferentiableAt ℝ
      (chartRepAt γ (fun y => parameterTangent (γ y)) x) x := by
    apply (mdifferentiableAt_tangentField_iff.mp ?_).2
    exact (contMDiff_parameterTangent.mdifferentiableAt (by decide)).comp x hγ
  have hvel : ∀ᶠ y in 𝓝 x,
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ y (1 : ℝ) : ℝ) =
        deriv θ y • parameterTangent (γ y) := by
    filter_upwards [hθ.eventually (by norm_num), heq.eventually_nhds] with y hy hyeq
    have hyeq : (fun s => (θ s : AddCircle (1 : ℝ))) =ᶠ[𝓝 y] γ := hyeq
    have hd := hy.differentiableAt (by norm_num)
    rw [← hyeq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))]
    have hcomp := mfderiv_comp y
      (contMDiff_coe.mdifferentiableAt (x := θ y) (by decide)) hd.mdifferentiableAt
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      ((fun s : ℝ => (s : AddCircle (1 : ℝ))) ∘ θ) y) 1 = _
    rw [hcomp, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) (θ y) (deriv θ y) = _
    rw [← hyeq.eq_of_nhds, parameterTangent_coe]
    let L : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) (θ y)
    change L (deriv θ y) = deriv θ y • L 1
    simpa only [smul_eq_mul, mul_one] using L.map_smul (deriv θ y) (1 : ℝ)
  rw [DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve flatMetric
    (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ y (1 : ℝ))
    (fun y => deriv θ y • parameterTangent (γ y)) Filter.EventuallyEq.rfl hvel]
  rw [covDerivAlong_smulFun flatMetric γ (deriv θ) _ x
    ((hθ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)) hV,
    covDerivAlong_parameterTangent_eq_zero hγ, smul_zero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.covDerivAlong_curveVelocity_of_local_lift then
    throwError "Refusing to shadow existing declaration AddCircle.covDerivAlong_curveVelocity_of_local_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.covDerivAlong_curveVelocity_of_local_lift ``Submission.AddCircle.covDerivAlong_curveVelocity_of_local_lift


end AddCircle
