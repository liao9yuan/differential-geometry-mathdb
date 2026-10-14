import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.PolarDivergence
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory _root_.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis


theorem laplacian_complex_eq_fderiv (f : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian f z =
      fderiv ℝ (fderiv ℝ f) z 1 1 +
      fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
  simp [_root_.InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_complex_eq_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_complex_eq_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_complex_eq_fderiv ``Submission.DifferentialGeometry.Analysis.laplacian_complex_eq_fderiv

private theorem fderiv_partial {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    fderiv ℝ (fun q => fderiv ℝ f q v) z w =
      fderiv ℝ (fderiv ℝ f) z w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.fderiv_partial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.fderiv_partial target :: scope.openDecls } }


theorem complexDivergence_gradient {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    complexDivergence (fun q => fderiv ℝ f q 1)
      (fun q => fderiv ℝ f q Complex.I) z = Laplacian.laplacian f z := by
  rw [complexDivergence, fderiv_partial hf, fderiv_partial hf,
    laplacian_complex_eq_fderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexDivergence_gradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexDivergence_gradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexDivergence_gradient ``Submission.DifferentialGeometry.Analysis.complexDivergence_gradient


theorem complexDivergence_green {u v : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) :
    complexDivergence
      (fun q => u q * fderiv ℝ v q 1 - v q * fderiv ℝ u q 1)
      (fun q => u q * fderiv ℝ v q Complex.I - v q * fderiv ℝ u q Complex.I) z =
      u z * Laplacian.laplacian v z - v z * Laplacian.laplacian u z := by
  have hu₁ := hu.differentiableAt (by norm_num)
  have hv₁ := hv.differentiableAt (by norm_num)
  have hdu (e : ℂ) : DifferentiableAt ℝ (fun q => fderiv ℝ u q e) z :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hdv (e : ℂ) : DifferentiableAt ℝ (fun q => fderiv ℝ v q e) z :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  unfold complexDivergence
  erw [fderiv_fun_sub (hu₁.mul (hdv 1)) (hv₁.mul (hdu 1)),
    fderiv_fun_sub (hu₁.mul (hdv Complex.I)) (hv₁.mul (hdu Complex.I)),
    fderiv_fun_mul hu₁ (hdv 1), fderiv_fun_mul hv₁ (hdu 1),
    fderiv_fun_mul hu₁ (hdv Complex.I), fderiv_fun_mul hv₁ (hdu Complex.I)]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_partial hu, fderiv_partial hv, laplacian_complex_eq_fderiv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexDivergence_green then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexDivergence_green"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexDivergence_green ``Submission.DifferentialGeometry.Analysis.complexDivergence_green


theorem apply_polar_unit (L : ℂ →L[ℝ] ℝ) (θ : ℝ) :
    L (Complex.polarCoord.symm (1, θ)) = Real.cos θ * L 1 + Real.sin θ * L Complex.I := by
  have h : Complex.polarCoord.symm (1, θ) =
      Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    simp [Complex.polarCoord_symm_apply, Complex.real_smul]
  rw [h, map_add, map_smul, map_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.apply_polar_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.apply_polar_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.apply_polar_unit ``Submission.DifferentialGeometry.Analysis.apply_polar_unit


def greenRadialFlux (u v : ℂ → ℝ) (r θ : ℝ) : ℝ :=
  let z := Complex.polarCoord.symm (r, θ)
  let e := Complex.polarCoord.symm (1, θ)
  r * (u z * fderiv ℝ v z e - v z * fderiv ℝ u z e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.greenRadialFlux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.greenRadialFlux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.greenRadialFlux ``Submission.DifferentialGeometry.Analysis.greenRadialFlux




theorem integral_green_annulus {u v : ℂ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hu : ∀ z, ‖z‖ ∈ _root_.Set.Icc r R → ContDiffAt ℝ 2 u z)
    (hv : ∀ z, ‖z‖ ∈ _root_.Set.Icc r R → ContDiffAt ℝ 2 v z) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R},
      u z * Laplacian.laplacian v z - v z * Laplacian.laplacian u z) =
      (∫ θ in -Real.pi..Real.pi, greenRadialFlux u v R θ) -
        ∫ θ in -Real.pi..Real.pi, greenRadialFlux u v r θ := by
  let F := fun z => u z * fderiv ℝ v z 1 - v z * fderiv ℝ u z 1
  let G := fun z => u z * fderiv ℝ v z Complex.I - v z * fderiv ℝ u z Complex.I
  have hreg (e : ℂ) (z : ℂ) (hz : ‖z‖ ∈ _root_.Set.Icc r R) :
      ContDiffAt ℝ 1 (fun q => u q * fderiv ℝ v q e - v q * fderiv ℝ u q e) z := by
    exact ((hu z hz |>.of_le (by norm_num)).mul
      (((hv z hz).fderiv_right (by norm_num)).clm_apply contDiffAt_const)).sub
      ((hv z hz |>.of_le (by norm_num)).mul
        (((hu z hz).fderiv_right (by norm_num)).clm_apply contDiffAt_const))
  have h := integral_complexDivergence_annulus hr hrR (hreg 1) (hreg Complex.I)
  have hflux (a θ : ℝ) :
      a * (F (Complex.polarCoord.symm (a, θ)) * Real.cos θ +
        G (Complex.polarCoord.symm (a, θ)) * Real.sin θ) = greenRadialFlux u v a θ := by
    simp only [greenRadialFlux, apply_polar_unit, F, G]
    ring
  change (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, complexDivergence F G z) = _ at h
  dsimp only [F, G] at hflux
  simp_rw [hflux] at h
  rw [← h]
  apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_Icc.preimage continuous_norm.measurable)
  intro z hz
  exact (complexDivergence_green (hu z hz) (hv z hz)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_green_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_green_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_green_annulus ``Submission.DifferentialGeometry.Analysis.integral_green_annulus

end DifferentialGeometry.Analysis
