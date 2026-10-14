import Submission.DifferentialGeometry.Geometry.Connection.Cylinder
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Operator
variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {f : ℝ → ℝ}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_comp_height (hf : ContDiff ℝ ∞ f) (x : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    mvfderiv (I.prod 𝓘(ℝ)) (fun y : M × ℝ => f y.2) x v = deriv f x.2 * v.2 := by
  have hd := (hf.differentiable (by simp)) x.2
  have h := mvfderiv_comp_apply (I := 𝓘(ℝ)) (I' := I.prod 𝓘(ℝ))
    (f := Prod.snd) (g := f) x hd.mdifferentiableAt mdifferentiableAt_snd v
  rw [mvfderiv_real_model_eq_fderiv, hd.hasDerivAt.hasFDerivAt.fderiv] at h
  rw [mfderiv_snd] at h
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  change mvfderiv (I.prod 𝓘(ℝ)) (fun y : M × ℝ => f y.2) x v = v.2 * deriv f x.2 at h
  exact h.trans (mul_comm _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.mvfderiv_comp_height
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.mvfderiv_comp_height target :: scope.openDecls } }

theorem gradFun_comp_height_cylinderMetric (g : SmoothRiemannianMetric I M)
    (hf : ContDiff ℝ ∞ f) (x : M × ℝ) :
    gradFun (cylinderMetric g) (fun y : M × ℝ => f y.2) x =
      deriv f x.2 • cylinderAxis x := by
  have h := gradientFun_comp (cylinderMetric g)
    ((hf.differentiable (by simp)) x.2) mdifferentiableAt_snd
  simpa only [gradient_eq_gradFun, gradFun_height_eq_cylinderAxis] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.gradFun_comp_height_cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.gradFun_comp_height_cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.gradFun_comp_height_cylinderMetric ``Submission.DifferentialGeometry.Geometry.Operator.gradFun_comp_height_cylinderMetric

theorem inner_gradFun_comp_height_cylinderMetric (g : SmoothRiemannianMetric I M)
    (hf : ContDiff ℝ ∞ f) (x : M × ℝ) :
    (cylinderMetric g).inner x (gradFun (cylinderMetric g) (fun y : M × ℝ => f y.2) x)
      (gradFun (cylinderMetric g) (fun y : M × ℝ => f y.2) x) = (deriv f x.2) ^ 2 := by
  rw [gradFun_comp_height_cylinderMetric g hf,
    ((cylinderMetric g).inner x).map_smul (deriv f x.2) (cylinderAxis x), smul_apply,
    ((cylinderMetric g).inner x (cylinderAxis x)).map_smul (deriv f x.2) (cylinderAxis x),
    cylinderMetric_axis_unit]
  simp only [smul_eq_mul, mul_one, pow_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.inner_gradFun_comp_height_cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.inner_gradFun_comp_height_cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.inner_gradFun_comp_height_cylinderMetric ``Submission.DifferentialGeometry.Geometry.Operator.inner_gradFun_comp_height_cylinderMetric

private theorem cov_gradFun_comp_height (g : SmoothRiemannianMetric I M)
    (hf : ContDiff ℝ ∞ f) (x : M × ℝ) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    (LeviCivita (cylinderMetric g)).toFun
      (fun y : M × ℝ => gradFun (cylinderMetric g) (fun p : M × ℝ => f p.2) y) x v =
        (deriv (deriv f) x.2 * v.2) • cylinderAxis x := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have haxis := (contMDiff_cylinderAxis (I := I) (M := M)).mdifferentiable (by simp) x
  have hcoeff : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun y : M × ℝ => deriv f y.2) x :=
    (hd.contMDiff.comp contMDiff_snd).mdifferentiable (by simp) x
  have hgrad : (fun y : M × ℝ => gradFun (cylinderMetric g) (fun p : M × ℝ => f p.2) y) =
      (fun y : M × ℝ => deriv f y.2) • cylinderAxis :=
    funext (gradFun_comp_height_cylinderMetric g hf)
  rw [hgrad]
  have h := congrArg (fun L => L v)
    ((LeviCivita (cylinderMetric g)).isCovariantDerivativeOnUniv.leibniz haxis hcoeff)
  change (LeviCivita (cylinderMetric g)).toFun
      ((fun y : M × ℝ => deriv f y.2) • cylinderAxis) x v = _ at h
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at h
  change _ = deriv f x.2 •
      leviCivitaConnectionOfMetric (cylinderMetric g) cylinderAxis x v +
        mvfderiv (I.prod 𝓘(ℝ)) (fun y : M × ℝ => deriv f y.2) x v • cylinderAxis x at h
  rw [leviCivita_cylinderAxis, smul_zero, zero_add, mvfderiv_comp_height hd] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.cov_gradFun_comp_height
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.cov_gradFun_comp_height target :: scope.openDecls } }

theorem hessFun_comp_height_cylinderMetric [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hf : ContDiff ℝ ∞ f) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    hessFun (cylinderMetric g) (fun y : M × ℝ => f y.2) x v w =
      deriv (deriv f) x.2 * v.2 * w.2 := by
  apply (hessFun_eq_cov_grad (cylinderMetric g)
    (show ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun y : M × ℝ => f y.2)
      from hf.contMDiff.comp contMDiff_snd) x v w).trans
  rw [cov_gradFun_comp_height g hf, map_smul, smul_apply, cylinderMetric_axis_inner]
  have hz : mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x w = w.2 := by
    simpa using mvfderiv_comp_height (I := I) (f := id) contDiff_id x w
  rw [hz]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.hessFun_comp_height_cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.hessFun_comp_height_cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.hessFun_comp_height_cylinderMetric ``Submission.DifferentialGeometry.Geometry.Operator.hessFun_comp_height_cylinderMetric

private theorem laplacian_height (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    laplacian (LeviCivita (cylinderMetric g)) (cylinderMetric g) Prod.snd x = 0 := by
  have hgrad : gradientFun (cylinderMetric g) Prod.snd = cylinderAxis :=
    funext (gradFun_height_eq_cylinderAxis g)
  rw [laplacian, hgrad, divergence]
  have hz : (LeviCivita (cylinderMetric g)).toFun cylinderAxis x = 0 := by
    ext v
    exact leviCivita_cylinderAxis g x v
  rw [hz]
  exact map_zero _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_height
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.laplacian_height target :: scope.openDecls } }

theorem laplacian_comp_height_cylinderMetric (g : SmoothRiemannianMetric I M)
    (hf : ContDiff ℝ ∞ f) (x : M × ℝ) :
    laplacian (LeviCivita (cylinderMetric g)) (cylinderMetric g)
      (fun y : M × ℝ => f y.2) x = deriv (deriv f) x.2 := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hs : MDiffAt (T% fun y : M × ℝ => gradientFun (cylinderMetric g) Prod.snd y) x := by
    simpa only [gradient_eq_gradFun, gradFun_height_eq_cylinderAxis] using
      (contMDiff_cylinderAxis (I := I) (M := M)).mdifferentiable (by simp) x
  have h := laplacian_comp (LeviCivita (cylinderMetric g)) (cylinderMetric g)
    (hf.differentiable (by simp)) ((hd.differentiable (by simp)) x.2)
    (fun _ => mdifferentiableAt_snd) hs
  rw [laplacian_height, gradient_eq_gradFun, gradFun_height_eq_cylinderAxis,
    cylinderMetric_axis_unit, _root_.MulZeroClass.mul_zero, zero_add, mul_one] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_comp_height_cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_comp_height_cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_comp_height_cylinderMetric ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_comp_height_cylinderMetric

theorem laplaceBeltrami_comp_height_cylinderMetric [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hf : ContDiff ℝ ∞ f) (x : M × ℝ) :
    ΔG (cylinderMetric g) ⟨fun y : M × ℝ => f y.2, hf.contMDiff.comp contMDiff_snd⟩ x =
      deriv (deriv f) x.2 := by
  rw [← laplacian_levi_eq]
  exact laplacian_comp_height_cylinderMetric g hf x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplaceBeltrami_comp_height_cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplaceBeltrami_comp_height_cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplaceBeltrami_comp_height_cylinderMetric ``Submission.DifferentialGeometry.Geometry.Operator.laplaceBeltrami_comp_height_cylinderMetric

end DifferentialGeometry.Geometry.Operator
