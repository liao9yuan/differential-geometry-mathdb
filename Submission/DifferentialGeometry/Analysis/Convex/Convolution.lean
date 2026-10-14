import Submission.DifferentialGeometry.Analysis.Convex.Integral
import Submission.DifferentialGeometry.Analysis.Convex.Differentiability
import Mathlib.Analysis.Calculus.ContDiff.Convolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Convolution

open _root_.ConvexOn in
theorem ConvexOn.convolution_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    {μ : _root_.MeasureTheory.Measure E} {κ f : E → ℝ} (hf : ConvexOn ℝ _root_.Set.univ f)
    (hκ : ∀ᵐ z ∂μ, 0 ≤ κ z)
    (hi : _root_.MeasureTheory.ConvolutionExists κ f (ContinuousLinearMap.lsmul ℝ ℝ) μ) :
    ConvexOn ℝ _root_.Set.univ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  apply convexOn_integral convex_univ _ (fun x _ => hi x)
  filter_upwards [hκ] with z hz
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have heq : (a • x + b • y) - z = a • (x - z) + b • (y - z) := by
    simp only [smul_sub]
    rw [sub_add_sub_comm, ← add_smul, hab, one_smul]
  change κ z * f ((a • x + b • y) - z) ≤ a * (κ z * f (x - z)) + b * (κ z * f (y - z))
  rw [heq]
  have h := mul_le_mul_of_nonneg_left (hf.2 (_root_.Set.mem_univ (x - z)) (_root_.Set.mem_univ (y - z)) ha hb hab) hz
  simpa only [smul_eq_mul, mul_add, mul_left_comm (κ z)] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.convolution_left then
    throwError "Refusing to shadow existing declaration ConvexOn.convolution_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.convolution_left ``Submission.ConvexOn.convolution_left

open _root_.ConvexOn in
theorem ConvexOn.convolution_add_quadratic
    {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    {μ : _root_.MeasureTheory.Measure E} {κ f : E → ℝ} (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hf : ConvexOn ℝ _root_.Set.univ (fun x => f x + (1 / 2 : ℝ) * B x x))
    (hκ : ∀ᵐ z ∂μ, 0 ≤ κ z) (hκi : _root_.MeasureTheory.Integrable κ μ)
    (hi : _root_.MeasureTheory.ConvolutionExists κ f (ContinuousLinearMap.lsmul ℝ ℝ) μ) :
    ConvexOn ℝ _root_.Set.univ (fun x => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x +
      (∫ z, κ z ∂μ) * ((1 / 2 : ℝ) * B x x)) := by
  let Q : E → ℝ := fun x => (1 / 2 : ℝ) * B x x
  have hconv (z : E) : ConvexOn ℝ _root_.Set.univ (fun x => f (x - z) + Q x) := by
    have hbase : ConvexOn ℝ _root_.Set.univ (fun x => f (x - z) + Q (x - z)) := by
      refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      have heq : (a • x + b • y) - z = a • (x - z) + b • (y - z) := by
        simp only [smul_sub]
        rw [sub_add_sub_comm, ← add_smul, hab, one_smul]
      change f ((a • x + b • y) - z) + Q ((a • x + b • y) - z) ≤ _
      rw [heq]
      exact hf.2 (_root_.Set.mem_univ _) (_root_.Set.mem_univ _) ha hb hab
    let D : E →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • (B z + B.flip z)
    have hlin := (D.convexOn convex_univ).sub (concaveOn_const (Q z) convex_univ)
    apply (hbase.add hlin).congr
    intro x _
    change f (x - z) + Q (x - z) + (D x - Q z) = f (x - z) + Q x
    simp only [Q, D, map_sub, LinearMap.sub_apply, LinearMap.flip_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hint (x : E) : _root_.MeasureTheory.Integrable (fun z => κ z * f (x - z)) μ := hi x
  have hi' (x : E) : _root_.MeasureTheory.Integrable (fun z => κ z * (f (x - z) + Q x)) μ := by
    have h : _root_.MeasureTheory.Integrable (fun z => κ z * f (x - z) + κ z * Q x) μ :=
      (hint x).add (hκi.mul_const (Q x))
    simpa only [mul_add] using h
  have h := convexOn_integral convex_univ
    (hκ.mono fun z hz => (hconv z).smul hz) (fun x _ => hi' x)
  apply h.congr
  intro x _
  change (∫ z, κ z * (f (x - z) + Q x) ∂μ) = _
  simp_rw [mul_add]
  rw [_root_.MeasureTheory.integral_add (hint x) (hκi.mul_const (Q x)), _root_.MeasureTheory.integral_mul_const]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.convolution_add_quadratic then
    throwError "Refusing to shadow existing declaration ConvexOn.convolution_add_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.convolution_add_quadratic ``Submission.ConvexOn.convolution_add_quadratic

open _root_.ConvexOn in
theorem ConvexOn.fderiv_fderiv_convolution_left_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E}
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {κ f : E → ℝ} (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : B.flip = B)
    (hf : ConvexOn ℝ _root_.Set.univ (fun x => f x + (1 / 2 : ℝ) * B x x))
    (hκ : ∀ᵐ z ∂μ, 0 ≤ κ z) (hκi : _root_.MeasureTheory.Integrable κ μ)
    (hκd : ContDiff ℝ 2 κ) (hκc : HasCompactSupport κ)
    (hfi : _root_.MeasureTheory.LocallyIntegrable f μ) (x v : E) :
    -(∫ z, κ z ∂μ) * B v v ≤
      fderiv ℝ (fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f)) x v v := by
  let g := κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f
  let m := ∫ z, κ z ∂μ
  let C := m • B
  let Q : E → ℝ := fun y => (1 / 2 : ℝ) * C y y
  have hCsym : C.flip = C := by change m • B.flip = m • B; rw [hB]
  have hQall := DifferentialGeometry.Analysis.second_order_polynomial_derivatives
    (0 : E) (0 : ℝ) (0 : E →L[ℝ] ℝ) C hCsym
  simp only [sub_zero, zero_apply, zero_add, smul_eq_mul] at hQall
  have hQ : ContDiff ℝ 2 Q := hQall.1.of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hQg : fderiv ℝ (fderiv ℝ Q) x = C := (hQall.2.2 x).2
  have hg : ContDiff ℝ 2 g := hκc.contDiff_convolution_left _ hκd hfi
  have hconv : ConvexOn ℝ _root_.Set.univ (fun y => g y + Q y) := by
    have h := hf.convolution_add_quadratic
      ((ContinuousLinearMap.coeLM ℝ).comp B.toLinearMap) hκ hκi
      (hκc.convolutionExists_left _ hκd.continuous hfi)
    convert h using 1
    funext y
    change g y + (1 / 2 : ℝ) * (m * B y y) = g y + m * ((1 / 2 : ℝ) * B y y)
    ring
  have hnonneg := hconv.fderiv_fderiv_nonneg (x := x) Filter.univ_mem
    ((hg.add hQ).differentiable (by norm_num)).differentiableOn
  have heq : fderiv ℝ (fun y => g y + Q y) = fderiv ℝ g + fderiv ℝ Q := by
    funext y
    exact fderiv_add (hg.differentiable (by norm_num) y) (hQ.differentiable (by norm_num) y)
  have h := hnonneg v
  rw [heq, fderiv_add ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    ((hQ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x), hQg] at h
  change 0 ≤ fderiv ℝ (fderiv ℝ g) x v v + m * B v v at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.fderiv_fderiv_convolution_left_lower_bound then
    throwError "Refusing to shadow existing declaration ConvexOn.fderiv_fderiv_convolution_left_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.fderiv_fderiv_convolution_left_lower_bound ``Submission.ConvexOn.fderiv_fderiv_convolution_left_lower_bound
