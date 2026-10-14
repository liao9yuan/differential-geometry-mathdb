import Submission.DifferentialGeometry.Geometry.Connection.ConformalEuclidean
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Gradient
import Submission.DifferentialGeometry.Geometry.Measure.Area.Riemannian
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.InnerProductSpace
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Curvature

private theorem real_inner_complex (v w : ℂ) :
    inner ℝ v w = v.re * w.re + v.im * w.im := by
  simp [Complex.inner, Complex.mul_re, mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.real_inner_complex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.real_inner_complex target :: scope.openDecls } }

private theorem covector_complex (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = v.re * L 1 + v.im * L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp [Complex.real_smul]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.covector_complex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.covector_complex target :: scope.openDecls } }

private theorem correction_one_re (f : ℂ → ℝ) (z w : ℂ) :
    (conformalEuclideanCorrection f z 1 w).re =
      fderiv ℝ f z 1 * w.re + fderiv ℝ f z Complex.I * w.im := by
  simp only [conformalEuclideanCorrection, Complex.add_re, Complex.sub_re,
    Complex.smul_re, smul_eq_mul, real_inner_complex, Complex.one_re,
    Complex.one_im, DifferentialGeometry.Analysis.gradient_complex_re, covector_complex (fderiv ℝ f z) w]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.correction_one_re
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.correction_one_re target :: scope.openDecls } }

private theorem correction_I_re (f : ℂ → ℝ) (z w : ℂ) :
    (conformalEuclideanCorrection f z Complex.I w).re =
      fderiv ℝ f z Complex.I * w.re - fderiv ℝ f z 1 * w.im := by
  simp only [conformalEuclideanCorrection, Complex.add_re, Complex.sub_re,
    Complex.smul_re, smul_eq_mul, real_inner_complex, Complex.I_re,
    Complex.I_im, DifferentialGeometry.Analysis.gradient_complex_re]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.correction_I_re
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.correction_I_re target :: scope.openDecls } }

private theorem correction_I_I (f : ℂ → ℝ) (z : ℂ) :
    conformalEuclideanCorrection f z Complex.I Complex.I =
      -(fderiv ℝ f z 1) • (1 : ℂ) + fderiv ℝ f z Complex.I • Complex.I := by
  apply Complex.ext <;>
    simp [conformalEuclideanCorrection, DifferentialGeometry.Analysis.gradient_complex_re,
      DifferentialGeometry.Analysis.gradient_complex_im]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.correction_I_I
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.correction_I_I target :: scope.openDecls } }

private theorem correction_one_I (f : ℂ → ℝ) (z : ℂ) :
    conformalEuclideanCorrection f z 1 Complex.I =
      fderiv ℝ f z Complex.I • (1 : ℂ) + fderiv ℝ f z 1 • Complex.I := by
  simp [conformalEuclideanCorrection, add_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.correction_one_I
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.correction_one_I target :: scope.openDecls } }

private theorem constant_field_smooth (v : ℂ) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun y => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.constant_field_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.constant_field_smooth target :: scope.openDecls } }

private theorem constant_field_bracket (v w z : ℂ) :
    VectorField.mlieBracket 𝓘(ℝ, ℂ) (fun _ => v) (fun _ => w) z = 0 := by
  erw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin]
  simp [VectorField.lieBracketWithin]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.constant_field_bracket
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.constant_field_bracket target :: scope.openDecls } }



theorem riemann_conformalPlane_re {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    (riemannOp (LeviCivita (conformalEuclideanMetric f hf))
      z (1 : ℂ) Complex.I Complex.I).re = -Laplacian.laplacian f z := by
  let C := LeviCivita (conformalEuclideanMetric f hf)
  let a : ℂ → ℝ := fun q => fderiv ℝ f q 1
  let b : ℂ → ℝ := fun q => fderiv ℝ f q Complex.I
  let A : ℂ → ℂ := fun q => -a q • (1 : ℂ) + b q • Complex.I
  let B : ℂ → ℂ := fun q => b q • (1 : ℂ) + a q • Complex.I
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have ha : DifferentiableAt ℝ a z :=
    (hdf.clm_apply contDiff_const).differentiable (by norm_num) z
  have hb : DifferentiableAt ℝ b z :=
    (hdf.clm_apply contDiff_const).differentiable (by norm_num) z
  have hA : DifferentiableAt ℝ A z := (ha.neg.smul_const 1).add (hb.smul_const Complex.I)
  have hB : DifferentiableAt ℝ B z := (hb.smul_const 1).add (ha.smul_const Complex.I)
  have hCA : covApply C (fun _ => Complex.I) (fun _ => Complex.I) = A := by
    funext q
    change LeviCivita (conformalEuclideanMetric f hf) (fun _ => Complex.I) q Complex.I = _
    rw [leviCivita_conformalEuclidean hf (differentiableAt_const _)]
    erw [fderiv_const]
    change (0 : ℂ) + conformalEuclideanCorrection f q Complex.I Complex.I = A q
    rw [zero_add]
    exact correction_I_I f q
  have hCB : covApply C (fun _ => (1 : ℂ)) (fun _ => Complex.I) = B := by
    funext q
    change LeviCivita (conformalEuclideanMetric f hf) (fun _ => Complex.I) q (1 : ℂ) = _
    rw [leviCivita_conformalEuclidean hf (differentiableAt_const _)]
    erw [fderiv_const]
    change (0 : ℂ) + conformalEuclideanCorrection f q 1 Complex.I = B q
    rw [zero_add]
    exact correction_one_I f q
  have hR := riemannOp_apply_smooth C (x := z)
    (constant_field_smooth 1) (constant_field_smooth Complex.I) (constant_field_smooth Complex.I)
  erw [riemannSec_def, hCA, hCB, constant_field_bracket, map_zero, sub_zero] at hR
  change riemannOp C z (1 : ℂ) Complex.I Complex.I = C A z (1 : ℂ) - C B z Complex.I at hR
  rw [hR]
  change (LeviCivita (conformalEuclideanMetric f hf) A z (1 : ℂ) -
    LeviCivita (conformalEuclideanMetric f hf) B z Complex.I).re = _
  rw [leviCivita_conformalEuclidean hf hA, leviCivita_conformalEuclidean hf hB]
  erw [Complex.sub_re, Complex.add_re, Complex.add_re, correction_one_re, correction_I_re]
  have hdA : (fderiv ℝ A z 1).re = -fderiv ℝ a z 1 := by
    have h := ((ha.hasFDerivAt.neg.smul_const (1 : ℂ)).add
      (hb.hasFDerivAt.smul_const Complex.I)).fderiv
    rw [show fderiv ℝ A z = _ from h]
    simp
  have hdB : (fderiv ℝ B z Complex.I).re = fderiv ℝ b z Complex.I := by
    have h := ((hb.hasFDerivAt.smul_const (1 : ℂ)).add
      (ha.hasFDerivAt.smul_const Complex.I)).fderiv
    rw [show fderiv ℝ B z = _ from h]
    simp
  have hΔ := DifferentialGeometry.Analysis.complexDivergence_gradient
    (hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) : ContDiffAt ℝ 2 f z)
  change fderiv ℝ a z 1 + fderiv ℝ b z Complex.I = Laplacian.laplacian f z at hΔ
  rw [hdA, hdB]
  simp only [A, B, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, smul_eq_mul,
    mul_one, _root_.MulZeroClass.mul_zero, add_zero, zero_add]
  dsimp [a, b] at hΔ ⊢
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemann_conformalPlane_re then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemann_conformalPlane_re"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemann_conformalPlane_re ``Submission.DifferentialGeometry.Geometry.riemann_conformalPlane_re



def planeGaussianCurvature (g : SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ) (z : ℂ) : ℝ :=
  metricRm04StandardAt g z (1 : ℂ) Complex.I Complex.I (1 : ℂ) /
    (g.inner z (1 : ℂ) (1 : ℂ) * g.inner z Complex.I Complex.I -
      g.inner z (1 : ℂ) Complex.I ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.planeGaussianCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.planeGaussianCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.planeGaussianCurvature ``Submission.DifferentialGeometry.Geometry.planeGaussianCurvature


theorem planeGaussianCurvature_conformal {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    planeGaussianCurvature (conformalEuclideanMetric f hf) z =
      -Real.exp (-2 * f z) * Laplacian.laplacian f z := by
  erw [planeGaussianCurvature, rm04_eq_inner_riem, conformalEuclideanMetric_inner,
    real_inner_complex, riemann_conformalPlane_re hf]
  simp only [conformalEuclideanMetric_inner, real_inner_complex, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, mul_one, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul,
    one_mul, add_zero, zero_add, zero_pow (by decide : 2 ≠ 0), sub_zero]
  rw [show -2 * f z = -(2 * f z) by ring, Real.exp_neg]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.planeGaussianCurvature_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.planeGaussianCurvature_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.planeGaussianCurvature_conformal ``Submission.DifferentialGeometry.Geometry.planeGaussianCurvature_conformal


theorem tangentTwoJacobian_conformalPlane {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    tangentTwoJacobian (conformalEuclideanMetric f hf) (x := z) (1 : ℂ) Complex.I =
      Real.exp (2 * f z) := by
  erw [tangentTwoJacobian_of_conformal]
  · simp [conformalEuclideanMetric_inner]
  · simp [conformalEuclideanMetric_inner]
  · simp [conformalEuclideanMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tangentTwoJacobian_conformalPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tangentTwoJacobian_conformalPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tangentTwoJacobian_conformalPlane ``Submission.DifferentialGeometry.Geometry.tangentTwoJacobian_conformalPlane



theorem planeGaussianCurvature_mul_areaDensity {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    planeGaussianCurvature (conformalEuclideanMetric f hf) z *
      tangentTwoJacobian (conformalEuclideanMetric f hf) (x := z) (1 : ℂ) Complex.I =
      -Laplacian.laplacian f z := by
  rw [planeGaussianCurvature_conformal hf, tangentTwoJacobian_conformalPlane hf,
    show -2 * f z = -(2 * f z) by ring, Real.exp_neg]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.planeGaussianCurvature_mul_areaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.planeGaussianCurvature_mul_areaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.planeGaussianCurvature_mul_areaDensity ``Submission.DifferentialGeometry.Geometry.planeGaussianCurvature_mul_areaDensity

end DifferentialGeometry.Geometry
