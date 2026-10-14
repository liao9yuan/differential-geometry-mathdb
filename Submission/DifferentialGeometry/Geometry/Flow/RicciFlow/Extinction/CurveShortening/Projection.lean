import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SweptAreaEstimates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProjectionFrontier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def ProductCurve.horizontalSpeedFraction (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) : ℝ :=
  Real.sqrt (1 - c.angle g lambda x t ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction

namespace ProductCurve

variable (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem inner_X_self (x t : ℝ) :
    c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
      (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
          (c.projection.X (I := I) x t) +
        lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 := by
  rw [inner]
  simp only [X]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem inner_X_self_nonneg (x t : ℝ) :
    0 ≤ c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) := by
  rw [inner_X_self]
  have h1 : 0 ≤ (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := by
    rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
    · simp only [h, map_zero]; rfl
    · exact ((g t).pos (c.projection.lift x t) _ h).le
  nlinarith [sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner_X_self_nonneg

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_sq (x t : ℝ) :
    c.speed g lambda x t ^ 2 =
      c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) :=
  Real.sq_sqrt (inner_X_self_nonneg c g lambda x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem projection_speed_sq (x t : ℝ) :
    c.projection.speed g x t ^ 2 =
      (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) := by
  rw [CurveMap.speed]
  exact Real.sq_sqrt (by
    rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
    · simp only [h, map_zero]; rfl
    · exact ((g t).pos (c.projection.lift x t) _ h).le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_sq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_eq (x t : ℝ) :
    c.angle g lambda x t =
      lambda * (c.speed g lambda x t)⁻¹ * deriv (fun z => c.y z t) x := by
  rw [angle, inner, unitTangent, verticalUnit]
  simp only [X, Prod.smul_fst, Prod.smul_snd, map_zero, smul_eq_mul]
  rcases eq_or_ne lambda 0 with h | h
  · rw [h]; simp
  · field_simp
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_eq

omit [TopologicalSpace M] [CompleteSpace E] in
theorem deriv_y_add_period (t x : ℝ) :
    deriv (fun z => c.y z t) (x + 1) = deriv (fun z => c.y z t) x := by
  rw [← deriv_comp_add_const (f := fun z => c.y z t) (a := 1) (x := x)]
  have h : (fun z => c.y (z + 1) t) = fun z => c.y z t + c.degree := by
    funext z
    rw [c.increment]
  rw [h, deriv_add_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.deriv_y_add_period then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.deriv_y_add_period"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.deriv_y_add_period ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.deriv_y_add_period

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_add_period {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    c.speed g lambda (x + 1) t = c.speed g lambda x t := by
  have hl : c.projection.lift (x + 1) t = c.projection.lift x t :=
    CurveMap.lift_add_period c.projection t x
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z : ℝ => c.projection.lift z t) (x + 1) :=
    (contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c.projection J hc.1 t ht)).mdifferentiableAt
      (by simp)
  have hX : c.projection.X (I := I) (x + 1) t = c.projection.X (I := I) x t :=
    CurveMap.X_add_period c.projection t x hγ
  have hy : deriv (fun z => c.y z t) (x + 1) = deriv (fun z => c.y z t) x :=
    deriv_y_add_period c t x
  simp only [ProductCurve.speed, ProductCurve.inner, ProductCurve.X]
  rw [hl, hX, hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_add_period then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_add_period"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_add_period ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_add_period

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_add_period {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    c.angle g lambda (x + 1) t = c.angle g lambda x t := by
  rw [ProductCurve.angle_eq, ProductCurve.angle_eq, speed_add_period c g lambda hc t ht x,
    deriv_y_add_period c t x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_add_period then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_add_period"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_add_period ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_add_period

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_mul_speed_periodic {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Function.Periodic (fun x => c.angle g lambda x t * c.speed g lambda x t) 1 := by
  intro x
  simp only [angle_add_period c g lambda hc t ht x, speed_add_period c g lambda hc t ht x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_mul_speed_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_mul_speed_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_mul_speed_periodic ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_mul_speed_periodic

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_periodic {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    Function.Periodic (fun x => c.speed g lambda x t) 1 :=
  fun x => speed_add_period c g lambda hc t ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_periodic ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_periodic

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem arcLength_period_eq_length {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (t : ℝ)
    (ht : t ∈ J) (x : ℝ) :
    c.arcLength g lambda x (x + 1) t = c.length g lambda t := by
  have h := (speed_periodic c g lambda hc t ht).intervalIntegral_add_eq x 0
  simpa [ProductCurve.arcLength, ProductCurve.length, ProductCurve.integral, one_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength_period_eq_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength_period_eq_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength_period_eq_length ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength_period_eq_length

omit [CompleteSpace E] in
theorem abs_ds_angle_le_curvature (x t : ℝ) :
    |c.ds g lambda (c.angle g lambda) x t| ≤ c.curvature g lambda x t := by
  have hcv2 : (c.curvatureVector g lambda x t).2 =
      (c.speed g lambda x t)⁻¹ *
        deriv (fun z => (c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z) x := by
    simp only [ProductCurve.curvatureVector, ProductCurve.Ds, ProductCurve.Dx,
      ProductCurve.unitTangent, ProductCurve.X, Prod.smul_snd, smul_eq_mul]
  have hle : lambda ^ 2 * ((c.curvatureVector g lambda x t).2 *
      (c.curvatureVector g lambda x t).2) ≤ c.curvatureSq g lambda x t := by
    have hnn := DifferentialGeometry.metric_inner_self_nonneg (g t) (c.projection.lift x t)
      ((c.curvatureVector g lambda x t).1)
    simp only [ProductCurve.curvatureSq, ProductCurve.normSq, ProductCurve.inner]
    nlinarith [hnn]
  have hsqrt : |lambda * (c.curvatureVector g lambda x t).2| ≤ c.curvature g lambda x t := by
    rw [ProductCurve.curvature, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    calc (lambda * (c.curvatureVector g lambda x t).2) ^ 2
        = lambda ^ 2 * ((c.curvatureVector g lambda x t).2 *
            (c.curvatureVector g lambda x t).2) := by ring
      _ ≤ c.curvatureSq g lambda x t := hle
  have hangle : (fun z => c.angle g lambda z t) =
      fun z => lambda * ((c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z) := by
    funext z
    rw [ProductCurve.angle_eq, mul_assoc]
  rw [ProductCurve.ds, hangle, deriv_const_mul_field]
  have hprod : (c.speed g lambda x t)⁻¹ *
      (lambda * deriv (fun z => (c.speed g lambda z t)⁻¹ *
        deriv (fun w => c.y w t) z) x) =
      lambda * ((c.speed g lambda x t)⁻¹ *
        deriv (fun z => (c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z) x) := by
    ring
  rw [hprod, ← hcv2]
  exact hsqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_ds_angle_le_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_ds_angle_le_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_ds_angle_le_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_ds_angle_le_curvature

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem projection_speed_eq {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    c.projection.speed g x t =
      c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t := by
  set sp : ℝ := c.speed g lambda x t with hsp
  set psp : ℝ := c.projection.speed g x t with hpsp
  set dy : ℝ := deriv (fun z => c.y z t) x with hdy
  set a : ℝ := c.angle g lambda x t with haeq
  set h : ℝ := c.horizontalSpeedFraction g lambda x t with hh
  have hsp_nonneg : 0 ≤ sp := c.speed_nonneg g lambda x t
  have hpsp_nonneg : 0 ≤ psp := c.projection.speed_nonneg g x t
  have hX : (c.projection.X (I := I) x t) ≠ 0 := hi x t ht
  have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := (g t).pos (c.projection.lift x t) _ hX
  have hsp_pos : 0 < sp := by
    rw [hsp, speed, Real.sqrt_pos, inner]
    simp only [X]
    nlinarith [hpos, sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]
  have hsp2_pos : 0 < sp ^ 2 := pow_pos hsp_pos 2
  have hsq : sp ^ 2 = psp ^ 2 + lambda ^ 2 * dy ^ 2 := by
    rw [hsp, hpsp, hdy, speed_sq, inner_X_self, projection_speed_sq]
  have ha : a = lambda * sp⁻¹ * dy := angle_eq c g lambda x t
  have ha2 : a ^ 2 = lambda ^ 2 * dy ^ 2 / sp ^ 2 := by
    rw [ha]
    field_simp [ne_of_gt hsp_pos]
  have hone : a ^ 2 ≤ 1 := by
    rw [ha2, div_le_one hsp2_pos]
    nlinarith [sq_nonneg psp]
  have hh2 : h ^ 2 = 1 - a ^ 2 := by
    rw [hh, haeq, horizontalSpeedFraction]
    exact Real.sq_sqrt (by linarith)
  have hkey : psp ^ 2 = (h * sp) ^ 2 := by
    rw [mul_pow, hh2]
    have hmul : a ^ 2 * sp ^ 2 = lambda ^ 2 * dy ^ 2 := by
      rw [ha2]
      field_simp
    nlinarith [hsq, hmul]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hkey with hcase | hcase
  · exact hcase
  · have hnonneg : 0 ≤ h * sp := mul_nonneg (Real.sqrt_nonneg _) hsp_nonneg
    have hzero : h * sp = 0 := by nlinarith
    rw [hcase, hzero, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_eq


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_pos {J : Set ℝ}
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.speed g lambda x t := by
  have hX : (c.projection.X (I := I) x t) ≠ 0 := hi x t ht
  have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := (g t).pos (c.projection.lift x t) _ hX
  rw [speed, Real.sqrt_pos, inner]
  simp only [X]
  nlinarith [hpos, sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_pos_of_immersedOn {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.speed g lambda x t := by
  have hX : c.X (I := I) x t ≠ 0 := hi x t ht
  rw [speed, Real.sqrt_pos, inner_X_self]
  rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
  · have hdy : deriv (fun z => c.y z t) x ≠ 0 := by
      intro hd
      exact hX (by simp [X, h, hd])
    have hzero : (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) = 0 := by simp [h]
    rw [hzero, zero_add]
    exact mul_pos (pow_pos hlambda 2) (sq_pos_of_ne_zero hdy)
  · have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) := (g t).pos _ _ h
    nlinarith [sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos_of_immersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos_of_immersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos_of_immersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_pos_of_immersedOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_pos {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.horizontalSpeedFraction g lambda x t := by
  have hsp := speed_pos c g lambda hi x t ht
  have hpsp := c.projection.speed_pos g hi x t ht
  have heq := projection_speed_eq c g lambda hlambda hi x t ht
  have hquot : c.horizontalSpeedFraction g lambda x t =
      c.projection.speed g x t / c.speed g lambda x t := by
    rw [heq]
    field_simp
  rw [hquot]
  exact div_pos hpsp hsp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_pos

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem unitTangent_fst_eq {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (c.unitTangent g lambda x t).1 =
      c.horizontalSpeedFraction g lambda x t • c.projection.unitTangent g x t := by
  have hsp_ne : c.speed g lambda x t ≠ 0 := ne_of_gt (speed_pos c g lambda hi x t ht)
  have hpsp_ne : c.projection.speed g x t ≠ 0 :=
    ne_of_gt (c.projection.speed_pos g hi x t ht)
  have hh_ne : c.horizontalSpeedFraction g lambda x t ≠ 0 :=
    ne_of_gt (horizontalSpeedFraction_pos c g lambda hlambda hi x t ht)
  have heq := projection_speed_eq c g lambda hlambda hi x t ht
  rw [unitTangent, X, Prod.smul_fst, CurveMap.unitTangent, smul_smul]
  congr 1
  field_simp
  rw [heq]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent_fst_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent_fst_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent_fst_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent_fst_eq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_sq_le_one (x t : ℝ) : c.angle g lambda x t ^ 2 ≤ 1 := by
  rcases eq_or_ne (c.speed g lambda x t) 0 with h0 | h0
  · have hang : c.angle g lambda x t = 0 := by
      rw [angle_eq c g lambda x t, h0]
      simp
    rw [hang]
    norm_num
  · have hang : c.angle g lambda x t * c.speed g lambda x t =
        lambda * deriv (fun z => c.y z t) x := by
      rw [angle_eq c g lambda x t]
      field_simp
    have hsp2 : c.speed g lambda x t ^ 2 =
        c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) :=
      speed_sq c g lambda x t
    have hinner : c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
        (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
            (c.projection.X (I := I) x t) +
          lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 :=
      inner_X_self c g lambda x t
    have hsq : (c.angle g lambda x t * c.speed g lambda x t) ^ 2 ≤
        c.speed g lambda x t ^ 2 := by
      rw [hang, mul_pow, hsp2, hinner]
      nlinarith [DifferentialGeometry.metric_inner_self_nonneg (g t) (c.projection.lift x t)
        (c.projection.X (I := I) x t)]
    have hpos : 0 < c.speed g lambda x t ^ 2 := by positivity
    have heq : c.angle g lambda x t ^ 2 =
        (c.angle g lambda x t * c.speed g lambda x t) ^ 2 / c.speed g lambda x t ^ 2 := by
      field_simp
    rw [heq]
    exact (div_le_one hpos).mpr hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_sq_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_sq_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_sq_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_sq_le_one

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_sq (x t : ℝ) :
    c.horizontalSpeedFraction g lambda x t ^ 2 = 1 - c.angle g lambda x t ^ 2 :=
  Real.sq_sqrt (by linarith [angle_sq_le_one c g lambda x t])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_sq_add (x t : ℝ) :
    c.speed g lambda x t ^ 2 =
      (c.projection.speed g x t) ^ 2 +
        lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 := by
  rw [speed_sq c g lambda x t, inner_X_self c g lambda x t,
    ← projection_speed_sq c g x t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_sq_add

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem projection_speed_le (x t : ℝ) :
    c.projection.speed g x t ≤ c.speed g lambda x t := by
  have hsq : c.projection.speed g x t ^ 2 ≤ c.speed g lambda x t ^ 2 := by
    rw [speed_sq_add]
    nlinarith [mul_nonneg (sq_nonneg lambda) (sq_nonneg (deriv (fun z => c.y z t) x))]
  calc c.projection.speed g x t = Real.sqrt (c.projection.speed g x t ^ 2) :=
        (Real.sqrt_sq (c.projection.speed_nonneg g x t)).symm
    _ ≤ Real.sqrt (c.speed g lambda x t ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c.speed g lambda x t := Real.sqrt_sq (c.speed_nonneg g lambda x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_speed_le

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem y_deriv_contDiff {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => deriv (fun w => c.y w t) z) := by
  have hslice : ContDiffOn ℝ ∞ (fun z : ℝ => c.y z t) univ :=
    hc.2.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun z _ => ⟨mem_univ z, ht⟩)
  have hderiv : ContDiffOn ℝ ∞
      (derivWithin (fun z : ℝ => c.y z t) _root_.Set.univ) univ :=
    hslice.derivWithin uniqueDiffOn_univ (by rw [ENat.coe_top_add_one])
  simpa only [derivWithin_univ] using contDiffOn_univ.mp hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.y_deriv_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.y_deriv_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.y_deriv_contDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.y_deriv_contDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_contDiff {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.projection.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => c.speed g lambda z t) := by
  have hp : ContDiff ℝ ∞ (fun z => c.projection.speed g z t) :=
    CurveMap.speed_contDiff g c.projection J hc.1 hi t ht
  have hd := y_deriv_contDiff c hc t ht
  have hu : ContDiff ℝ ∞ (fun z => (c.projection.speed g z t) ^ 2 +
      lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2) :=
    (hp.pow 2).add ((contDiff_const (c := lambda ^ 2)).mul (hd.pow 2))
  have hne : ∀ z, (c.projection.speed g z t) ^ 2 +
      lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2 ≠ 0 := by
    intro z
    have hpos : 0 < c.projection.speed g z t ^ 2 +
        lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2 := by
      rw [← speed_sq_add c g lambda z t]
      exact pow_pos (speed_pos c g lambda hi z t ht) 2
    exact ne_of_gt hpos
  have hsqrt := hu.sqrt hne
  have hfun : (fun z => c.speed g lambda z t) = fun z => Real.sqrt
      ((c.projection.speed g z t) ^ 2 + lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2) := by
    funext z
    rw [← speed_sq_add c g lambda z t, Real.sqrt_sq (c.speed_nonneg g lambda z t)]
  rw [hfun]
  exact hsqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_contDiff_of_immersedOn {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => c.speed g lambda z t) := by
  have hsq : ContDiff ℝ ∞ (fun z => (c.projection.speed g z t) ^ 2 +
      lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2) :=
    (CurveMap.speed_sq_contDiff g c.projection J hc.1 t ht).add
      ((contDiff_const (c := lambda ^ 2)).mul ((y_deriv_contDiff c hc t ht).pow 2))
  have hfun : (fun z => c.speed g lambda z t) = fun z => Real.sqrt
      ((c.projection.speed g z t) ^ 2 + lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2) := by
    funext z
    rw [← speed_sq_add c g lambda z t, Real.sqrt_sq (c.speed_nonneg g lambda z t)]
  rw [hfun]
  exact hsq.sqrt (fun z => ne_of_gt (by
    rw [← speed_sq_add c g lambda z t]
    exact pow_pos (speed_pos_of_immersedOn c g lambda hlambda hi z t ht) 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff_of_immersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff_of_immersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff_of_immersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_contDiff_of_immersedOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_contDiff_of_immersedOn {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => c.angle g lambda z t) := by
  have hs := speed_contDiff_of_immersedOn c g lambda hlambda hc hi t ht
  have hd := y_deriv_contDiff c hc t ht
  have hfun : (fun z => c.angle g lambda z t) =
      fun z => lambda * (c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z := by
    funext z
    rw [angle_eq]
  rw [hfun]
  exact (contDiff_const.mul (hs.inv fun z =>
    ne_of_gt (speed_pos_of_immersedOn c g lambda hlambda hi z t ht))).mul hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_contDiff_of_immersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_contDiff_of_immersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_contDiff_of_immersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle_contDiff_of_immersedOn

omit [CompleteSpace E] in
theorem abs_angle_sub_le_mul_arcLength {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) {t : ℝ} (ht : t ∈ J)
    {K x y : ℝ} (hcurv : ∀ z, c.curvature g lambda z t ≤ K) (hxy : x ≤ y) :
    |c.angle g lambda y t - c.angle g lambda x t| ≤ K * c.arcLength g lambda x y t := by
  have hcd := angle_contDiff_of_immersedOn c g lambda hlambda hc hi t ht
  have hdiff : ∀ z ∈ _root_.Set.uIcc x y, DifferentiableAt ℝ (fun z => c.angle g lambda z t) z :=
    fun z _ => (hcd.differentiable (by norm_num)).differentiableAt
  have hcont : Continuous (fun z => deriv (fun z => c.angle g lambda z t) z) :=
    hcd.continuous_deriv (by norm_num)
  have hFTC : (∫ z in x..y, deriv (fun z => c.angle g lambda z t) z) =
      c.angle g lambda y t - c.angle g lambda x t :=
    intervalIntegral.integral_deriv_eq_sub hdiff (hcont.intervalIntegrable x y)
  have hbound : ∀ z ∈ _root_.Set.Icc x y, |deriv (fun z => c.angle g lambda z t) z| ≤
      K * c.speed g lambda z t := by
    intro z _
    have hds := abs_ds_angle_le_curvature c g lambda z t
    rw [ProductCurve.ds] at hds
    have hsp := speed_pos_of_immersedOn c g lambda hlambda hi z t ht
    rw [abs_mul, abs_inv, abs_of_pos hsp, inv_mul_eq_div, div_le_iff₀ hsp] at hds
    exact hds.trans (mul_le_mul_of_nonneg_right (hcurv z) (c.speed_nonneg g lambda z t))
  have hspeed := (speed_contDiff_of_immersedOn c g lambda hlambda hc hi t ht).continuous
  calc |c.angle g lambda y t - c.angle g lambda x t|
      = |∫ z in x..y, deriv (fun z => c.angle g lambda z t) z| := by rw [hFTC]
    _ ≤ ∫ z in x..y, |deriv (fun z => c.angle g lambda z t) z| :=
        intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ z in x..y, K * c.speed g lambda z t :=
        intervalIntegral.integral_mono_on hxy (hcont.abs.intervalIntegrable x y)
          ((continuous_const.mul hspeed).intervalIntegrable x y) hbound
    _ = K * c.arcLength g lambda x y t := by
        rw [intervalIntegral.integral_const_mul, ProductCurve.arcLength]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_angle_sub_le_mul_arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_angle_sub_le_mul_arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_angle_sub_le_mul_arcLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.abs_angle_sub_le_mul_arcLength

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_contDiff {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => c.horizontalSpeedFraction g lambda z t) := by
  have hp : ContDiff ℝ ∞ (fun z => c.projection.speed g z t) :=
    CurveMap.speed_contDiff g c.projection J hc.1 hi t ht
  have hs := speed_contDiff c g lambda hc hi t ht
  have hdiv := hp.div hs (fun z => ne_of_gt (speed_pos c g lambda hi z t ht))
  have hfun : (fun z => c.horizontalSpeedFraction g lambda z t) =
      fun z => c.projection.speed g z t / c.speed g lambda z t := by
    funext z
    have hspeed_c : c.speed g lambda z t ≠ 0 := ne_of_gt (speed_pos c g lambda hi z t ht)
    rw [projection_speed_eq c g lambda hlambda hi z t ht]
    field_simp
  rw [hfun]
  exact hdiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_contDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_contDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_deriv_contDiff {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun x => deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) := by
  have hh := horizontalSpeedFraction_contDiff c g lambda hlambda hc hi t ht
  have hderiv : ContDiffOn ℝ ∞
      (derivWithin (fun z : ℝ => c.horizontalSpeedFraction g lambda z t) _root_.Set.univ) univ :=
    hh.contDiffOn.derivWithin uniqueDiffOn_univ (by rw [ENat.coe_top_add_one])
  simpa only [derivWithin_univ] using contDiffOn_univ.mp hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_deriv_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_deriv_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_deriv_contDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_deriv_contDiff

section

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

omit [CompleteSpace E] in
theorem projection_velocity_sub_curvature [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.projection.velocity J x t - c.projection.curvatureVector g x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) •
          c.projection.unitTangent g x t +
        (c.horizontalSpeedFraction g lambda x t ^ 2 - 1) •
          c.projection.curvatureVector g x t := by
  have hspeed_ne_n : c.speed g lambda x t ≠ 0 := ne_of_gt (speed_pos c g lambda hi x t ht)
  have hpspn : c.projection.speed g x t ≠ 0 :=
    ne_of_gt (c.projection.speed_pos g hi x t ht)
  have hpsp : c.projection.speed g x t =
      c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t :=
    projection_speed_eq c g lambda hlambda hi x t ht
  have hsec : (fun z => (c.unitTangent g lambda z t).1) =
      fun z => c.horizontalSpeedFraction g lambda z t • c.projection.unitTangent g z t :=
    funext (fun z => unitTangent_fst_eq c g lambda hlambda hi z t ht)
  have hhd : DifferentiableAt ℝ (fun z => c.horizontalSpeedFraction g lambda z t) x :=
    ((horizontalSpeedFraction_contDiff c g lambda hlambda hc.smooth hi t ht).contDiffAt).differentiableAt
      (by simp)
  have htau_rep_diff : DifferentiableAt ℝ (chartRepAt (I := I) (fun z => c.projection.lift z t)
      (fun z => c.projection.unitTangent g z t) x) x :=
    chartRep_diff (fun z => c.projection.lift z t)
      (fun z => c.projection.unitTangent g z t)
      (CurveMap.unitTangent_contMDiff g c.projection J hc.smooth.1 hi t ht) x
  have hgrad :=
    covDerivAlong_smulFun
        (g t) (fun z => c.projection.lift z t)
      (fun z => c.horizontalSpeedFraction g lambda z t)
      (fun z => c.projection.unitTangent g z t) x hhd htau_rep_diff
  have hvel : c.projection.velocity J x t = (c.curvatureVector g lambda x t).1 := by
    have h := congrArg Prod.fst (hc.equation x t ht)
    simpa only [velocity] using h
  have hcv : (c.curvatureVector g lambda x t).1 =
      (c.speed g lambda x t)⁻¹ • covDerivAlong (g t) (fun z => c.projection.lift z t)
        (fun z => (c.unitTangent g lambda z t).1) x := by
    simp only [ProductCurve.curvatureVector, ProductCurve.Ds, ProductCurve.Dx, Prod.smul_fst]
  have hgrad' : covDerivAlong (g t) (fun z => c.projection.lift z t)
      (fun z => (c.unitTangent g lambda z t).1) x =
      deriv (fun z => c.horizontalSpeedFraction g lambda z t) x •
          c.projection.unitTangent g x t +
        c.horizontalSpeedFraction g lambda x t •
          covDerivAlong (g t) (fun z => c.projection.lift z t)
            (fun z => c.projection.unitTangent g z t) x := by
    rw [hsec]
    exact hgrad
  have hk : c.projection.curvatureVector g x t =
      (c.projection.speed g x t)⁻¹ •
        covDerivAlong (g t) (fun z => c.projection.lift z t)
          (fun z => c.projection.unitTangent g z t) x := by
    simp only [CurveMap.curvatureVector, CurveMap.Ds, CurveMap.Dx]
  have hdtau : covDerivAlong (g t) (fun z => c.projection.lift z t)
      (fun z => c.projection.unitTangent g z t) x =
      c.projection.speed g x t • c.projection.curvatureVector g x t := by
    rw [hk, smul_smul, mul_inv_cancel₀ hpspn, one_smul]
  have hscl : (c.speed g lambda x t)⁻¹ *
      (c.horizontalSpeedFraction g lambda x t * c.projection.speed g x t) =
      c.horizontalSpeedFraction g lambda x t ^ 2 := by
    rw [hpsp]
    calc (c.speed g lambda x t)⁻¹ *
          (c.horizontalSpeedFraction g lambda x t *
            (c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t))
        = c.horizontalSpeedFraction g lambda x t ^ 2 *
          ((c.speed g lambda x t)⁻¹ * c.speed g lambda x t) := by ring
      _ = c.horizontalSpeedFraction g lambda x t ^ 2 := by
          rw [inv_mul_cancel₀ hspeed_ne_n, mul_one]
  rw [hvel, hcv, hgrad', hdtau]
  simp only [smul_add, smul_smul]
  rw [hscl]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_velocity_sub_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_velocity_sub_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_velocity_sub_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_velocity_sub_curvature

theorem projection_normalVelocityError [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.projection.normalVelocityError g J x t =
      -(c.angle g lambda x t ^ 2) • c.projection.curvatureVector g x t := by
  have htan := tangent_curvature_geometry g c.projection J hc.smooth.1 hi x t ht
  have htau_tau := htan.1
  have hkappa_tau := htan.2.1
  have hW := projection_velocity_sub_curvature c g lambda hlambda hc hi x t ht
  have hinner : (g t).inner (c.projection.lift x t)
    (c.projection.velocity J x t - c.projection.curvatureVector g x t)
      (c.projection.unitTangent g x t) =
      (c.speed g lambda x t)⁻¹ *
        deriv (fun z => c.horizontalSpeedFraction g lambda z t) x := by
    rw [hW]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, htau_tau, hkappa_tau, mul_one, _root_.MulZeroClass.mul_zero, add_zero]
  have hHS : c.horizontalSpeedFraction g lambda x t ^ 2 - 1 =
      -(c.angle g lambda x t ^ 2) := by
    rw [horizontalSpeedFraction_sq]
    ring
  simp only [CurveMap.normalVelocityError]
  rw [hinner, hW, hHS]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_normalVelocityError then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_normalVelocityError"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_normalVelocityError ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_normalVelocityError

theorem horizontalSpeedFraction_sq_mul_projection_curvature_le
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.horizontalSpeedFraction g lambda x t ^ 2 * c.projection.curvature g x t ≤
      c.curvature g lambda x t := by
  have htan := tangent_curvature_geometry g c.projection J hc.smooth.1 hi x t ht
  have htau_tau := htan.1
  have hkappa_tau := htan.2.1
  have htau_kappa : (g t).inner (c.projection.lift x t) (c.projection.unitTangent g x t)
      (c.projection.curvatureVector g x t) = 0 := by
    rw [← (g t).symm (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.unitTangent g x t)]
    exact hkappa_tau
  have hkk : (g t).inner (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.curvatureVector g x t) = c.projection.curvatureSq g x t := rfl
  have hW := projection_velocity_sub_curvature c g lambda hlambda hc hi x t ht
  have hvel : c.projection.velocity J x t = (c.curvatureVector g lambda x t).1 := by
    have h := congrArg Prod.fst (hc.equation x t ht)
    simpa only [velocity] using h
  have hK1 : c.projection.velocity J x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) •
          c.projection.unitTangent g x t +
        c.horizontalSpeedFraction g lambda x t ^ 2 •
          c.projection.curvatureVector g x t := by
    rw [← sub_add_cancel (c.projection.velocity J x t)
      (c.projection.curvatureVector g x t), hW]
    module
  have h11 : (g t).inner (c.projection.lift x t) (c.projection.velocity J x t)
      (c.projection.velocity J x t) =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
          c.projection.curvatureSq g x t := by
    rw [hK1]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, htau_tau, hkappa_tau, htau_kappa, hkk]
    ring
  have hcsq : c.curvatureSq g lambda x t =
      (g t).inner (c.projection.lift x t) (c.projection.velocity J x t)
          (c.projection.velocity J x t) +
        lambda ^ 2 * (c.curvatureVector g lambda x t).2 ^ 2 := by
    rw [hvel]
    simp only [ProductCurve.curvatureSq, ProductCurve.normSq, ProductCurve.inner]
    ring
  have hle : (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
      c.projection.curvatureSq g x t ≤ c.curvatureSq g lambda x t := by
    rw [hcsq, h11]
    nlinarith [sq_nonneg ((c.speed g lambda x t)⁻¹ *
        deriv (fun z => c.horizontalSpeedFraction g lambda z t) x),
      sq_nonneg (lambda * (c.curvatureVector g lambda x t).2)]
  have hsqrt : c.horizontalSpeedFraction g lambda x t ^ 2 * c.projection.curvature g x t =
      Real.sqrt ((c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
        c.projection.curvatureSq g x t) := by
    have hcs : c.projection.curvatureSq g x t = c.projection.curvature g x t ^ 2 :=
      (CurveMap.curvature_sq c.projection g x t).symm
    rw [hcs]
    have hsq : (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
        c.projection.curvature g x t ^ 2 =
        (c.horizontalSpeedFraction g lambda x t ^ 2 *
          c.projection.curvature g x t) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (mul_nonneg (sq_nonneg _) (c.projection.curvature_nonneg g x t))]
  calc c.horizontalSpeedFraction g lambda x t ^ 2 * c.projection.curvature g x t
      = Real.sqrt ((c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
          c.projection.curvatureSq g x t) := hsqrt
    _ ≤ Real.sqrt (c.curvatureSq g lambda x t) := Real.sqrt_le_sqrt hle
    _ = c.curvature g lambda x t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le

theorem curvatureSq_eq [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.curvatureSq g lambda x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        c.horizontalSpeedFraction g lambda x t ^ 4 * c.projection.curvatureSq g x t +
        lambda ^ 2 * ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => (c.speed g lambda z t)⁻¹ *
            deriv (fun w => c.y w t) z) x) ^ 2 := by
  have htan := tangent_curvature_geometry g c.projection J hc.smooth.1 hi x t ht
  have htau_tau := htan.1
  have hkappa_tau := htan.2.1
  have htau_kappa : (g t).inner (c.projection.lift x t) (c.projection.unitTangent g x t)
      (c.projection.curvatureVector g x t) = 0 := by
    rw [← (g t).symm (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.unitTangent g x t)]
    exact hkappa_tau
  have hkk : (g t).inner (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.curvatureVector g x t) = c.projection.curvatureSq g x t := rfl
  have hvel : c.projection.velocity J x t = (c.curvatureVector g lambda x t).1 := by
    have h := congrArg Prod.fst (hc.equation x t ht)
    simpa only [velocity] using h
  have hW := projection_velocity_sub_curvature c g lambda hlambda hc hi x t ht
  have hK1 : c.projection.velocity J x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) •
          c.projection.unitTangent g x t +
        c.horizontalSpeedFraction g lambda x t ^ 2 •
          c.projection.curvatureVector g x t := by
    rw [← sub_add_cancel (c.projection.velocity J x t)
      (c.projection.curvatureVector g x t), hW]
    module
  have hK2 : (c.curvatureVector g lambda x t).2 =
      (c.speed g lambda x t)⁻¹ *
        deriv (fun z => (c.speed g lambda z t)⁻¹ *
          deriv (fun w => c.y w t) z) x := by
    simp only [ProductCurve.curvatureVector, ProductCurve.Ds, ProductCurve.Dx,
      ProductCurve.unitTangent, ProductCurve.X, Prod.smul_snd, smul_eq_mul]
  have hu : (g t).inner (c.projection.lift x t) (c.projection.velocity J x t)
      (c.projection.velocity J x t) =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
          c.projection.curvatureSq g x t := by
    rw [hK1]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, htau_tau, hkappa_tau, htau_kappa, hkk]
    ring
  rw [ProductCurve.curvatureSq, ProductCurve.normSq, ProductCurve.inner, ← hvel, hK2, hu]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_eq

theorem curvatureSq_continuous [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Continuous (fun x => c.curvatureSq g lambda x t) := by
  have hspeed_c := speed_contDiff c g lambda hc.smooth hi t ht
  have hspeed_ne_n : ∀ z, c.speed g lambda z t ≠ 0 := fun z =>
    ne_of_gt (speed_pos c g lambda hi z t ht)
  have hdh := horizontalSpeedFraction_deriv_contDiff c g lambda hlambda hc.smooth hi t ht
  have hh := horizontalSpeedFraction_contDiff c g lambda hlambda hc.smooth hi t ht
  have hk := CurveMap.curvatureSq_contDiff g c.projection J hc.smooth.1 hi t ht
  have hdy := y_deriv_contDiff c hc.smooth t ht
  have hK2 : ContDiff ℝ ∞ (fun x => deriv (fun z => (c.speed g lambda z t)⁻¹ *
      deriv (fun w => c.y w t) z) x) := by
    have hinner : ContDiff ℝ ∞ (fun z => (c.speed g lambda z t)⁻¹ *
        deriv (fun w => c.y w t) z) := (hspeed_c.inv hspeed_ne_n).mul hdy
    have hd := hinner.contDiffOn.derivWithin uniqueDiffOn_univ
      (by rw [ENat.coe_top_add_one])
    simpa only [derivWithin_univ] using contDiffOn_univ.mp hd
  have hformula : (fun x => c.curvatureSq g lambda x t) = fun x =>
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        c.horizontalSpeedFraction g lambda x t ^ 4 * c.projection.curvatureSq g x t +
        lambda ^ 2 * ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => (c.speed g lambda z t)⁻¹ *
            deriv (fun w => c.y w t) z) x) ^ 2 :=
    by
    funext x
    exact curvatureSq_eq c g lambda hlambda hc hi x t ht
  rw [hformula]
  exact (((((hspeed_c.inv hspeed_ne_n).mul hdh).pow 2).add ((hh.pow 4).mul hk)).add
    ((contDiff_const (c := lambda ^ 2)).mul (((hspeed_c.inv hspeed_ne_n).mul hK2).pow 2))).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq_continuous

theorem curvature_continuous [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Continuous (fun x => c.curvature g lambda x t) :=
  Real.continuous_sqrt.comp (curvatureSq_continuous c g lambda hlambda hc hi t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_continuous

theorem curvature_mul_speed_integrable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    IntervalIntegrable (fun x => c.curvature g lambda x t * c.speed g lambda x t)
      volume 0 1 :=
  ((curvature_continuous c g lambda hlambda hc hi t ht).mul
    (speed_contDiff c g lambda hc.smooth hi t ht).continuous).intervalIntegrable 0 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_mul_speed_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_mul_speed_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_mul_speed_integrable ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_mul_speed_integrable

end

end ProductCurve

variable [SigmaCompactSpace M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [hBoundary : I.Boundaryless]
variable {D : RealTimeInterval} {a b s v : ℝ}

include hT2 hCompact hNonempty hBoundary

theorem rfs_csf_projected_ramp (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : _root_.Set.Icc s v ⊆ _root_.Set.Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (_root_.Set.Icc s v))
    (eta : ℝ) (heta : 0 < eta) (heta_one : eta < 1)
    (hu : ∀ x t, t ∈ _root_.Set.Icc s v →
      0 < c.angle B.family.metric lambda x t ∧ c.angle B.family.metric lambda x t ≤ eta) :
    (∀ x t, t ∈ _root_.Set.Icc s v →
      0 < c.horizontalSpeedFraction B.family.metric lambda x t ∧
      (c.unitTangent B.family.metric lambda x t).1 =
        c.horizontalSpeedFraction B.family.metric lambda x t •
          c.projection.unitTangent B.family.metric x t ∧
      c.projection.speed B.family.metric x t =
        c.horizontalSpeedFraction B.family.metric lambda x t * c.speed B.family.metric lambda x t ∧
      c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v) x t =
        -(c.angle B.family.metric lambda x t ^ 2) • c.projection.curvatureVector B.family.metric x t ∧
      c.horizontalSpeedFraction B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t ≤ c.curvature B.family.metric lambda x t) ∧
    (∀ t ∈ _root_.Set.Icc s v,
      c.projection.areaError B.family.metric (_root_.Set.Icc s v) t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.totalCurvature B.family.metric lambda t) := by
  let _ := hsv
  let _ := hwindow
  let _ := hCompact
  let _ := hNonempty
  constructor
  · intro x t ht
    exact ⟨ProductCurve.horizontalSpeedFraction_pos c B.family.metric lambda hlambda hi x t ht,
      ProductCurve.unitTangent_fst_eq c B.family.metric lambda hlambda hi x t ht,
      ProductCurve.projection_speed_eq c B.family.metric lambda hlambda hi x t ht,
      ProductCurve.projection_normalVelocityError c B.family.metric lambda hlambda hc hi x t ht,
      ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le c B.family.metric
        lambda hlambda hc hi x t ht⟩
  · intro t ht
    have heta_sqrt_pos : 0 < Real.sqrt (1 - eta ^ 2) :=
      Real.sqrt_pos.2 (by nlinarith [heta_one, sq_nonneg eta])
    have hpoint : ∀ x, Real.sqrt (c.projection.normSq B.family.metric
          (c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v)) x t) *
          c.projection.speed B.family.metric x t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          (c.curvature B.family.metric lambda x t * c.speed B.family.metric lambda x t) := by
      intro x
      have hNVE := ProductCurve.projection_normalVelocityError c B.family.metric lambda
        hlambda hc hi x t ht
      have ha2 : 0 ≤ c.angle B.family.metric lambda x t ^ 2 := sq_nonneg _
      have hnorm : c.projection.normSq B.family.metric
          (c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v)) x t =
          (c.angle B.family.metric lambda x t ^ 2) ^ 2 *
            c.projection.curvatureSq B.family.metric x t := by
        dsimp only [CurveMap.normSq, CurveMap.curvatureSq]
        rw [hNVE]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      have hsqrt : Real.sqrt (c.projection.normSq B.family.metric
            (c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v)) x t) =
          c.angle B.family.metric lambda x t ^ 2 *
            c.projection.curvature B.family.metric x t := by
        rw [hnorm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
        rfl
      have hhpos : 0 < c.horizontalSpeedFraction B.family.metric lambda x t :=
        ProductCurve.horizontalSpeedFraction_pos c B.family.metric lambda hlambda hi x t ht
      have hpsp : c.projection.speed B.family.metric x t =
          c.horizontalSpeedFraction B.family.metric lambda x t *
            c.speed B.family.metric lambda x t :=
        ProductCurve.projection_speed_eq c B.family.metric lambda hlambda hi x t ht
      have h1 : c.projection.curvature B.family.metric x t *
          (c.horizontalSpeedFraction B.family.metric lambda x t *
            c.horizontalSpeedFraction B.family.metric lambda x t) ≤
          c.curvature B.family.metric lambda x t := by
        nlinarith [ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le
          c B.family.metric lambda hlambda hc hi x t ht]
      have hAk : c.angle B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t *
          (c.horizontalSpeedFraction B.family.metric lambda x t *
            c.horizontalSpeedFraction B.family.metric lambda x t) ≤
          c.angle B.family.metric lambda x t ^ 2 *
            c.curvature B.family.metric lambda x t := by
        nlinarith [mul_le_mul_of_nonneg_left h1 ha2]
      have heta_sq_nonneg : 0 ≤ eta ^ 2 := sq_nonneg eta
      have hh_ge : Real.sqrt (1 - eta ^ 2) ≤
          c.horizontalSpeedFraction B.family.metric lambda x t := by
        rw [ProductCurve.horizontalSpeedFraction]
        refine Real.sqrt_le_sqrt ?_
        have h2 : c.angle B.family.metric lambda x t ^ 2 ≤ eta ^ 2 :=
          by
            nlinarith [mul_self_le_mul_self (hu x t ht).1.le (hu x t ht).2]
        linarith
      have hAh : c.angle B.family.metric lambda x t ^ 2 ≤
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            c.horizontalSpeedFraction B.family.metric lambda x t := by
        have h2 : c.angle B.family.metric lambda x t ^ 2 ≤ eta ^ 2 :=
          by
            nlinarith [mul_self_le_mul_self (hu x t ht).1.le (hu x t ht).2]
        have h3 : 1 ≤ c.horizontalSpeedFraction B.family.metric lambda x t /
            Real.sqrt (1 - eta ^ 2) := (one_le_div heta_sqrt_pos).mpr hh_ge
        have h4 : eta ^ 2 ≤ eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            c.horizontalSpeedFraction B.family.metric lambda x t := by
          calc eta ^ 2 = eta ^ 2 * 1 := by ring
            _ ≤ eta ^ 2 * (c.horizontalSpeedFraction B.family.metric lambda x t /
                Real.sqrt (1 - eta ^ 2)) := mul_le_mul_of_nonneg_left h3 heta_sq_nonneg
            _ = eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
                c.horizontalSpeedFraction B.family.metric lambda x t := by ring
        linarith
      have hAC : c.angle B.family.metric lambda x t ^ 2 *
          c.curvature B.family.metric lambda x t ≤
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            (c.curvature B.family.metric lambda x t *
              c.horizontalSpeedFraction B.family.metric lambda x t) := by
        have h := mul_le_mul_of_nonneg_right hAh (c.curvature_nonneg B.family.metric lambda x t)
        nlinarith [h]
      have hfin : c.angle B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t *
          c.horizontalSpeedFraction B.family.metric lambda x t ≤
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.curvature B.family.metric lambda x t := by
        refine le_of_mul_le_mul_right ?_ hhpos
        nlinarith [hAk.trans hAC]
      rw [hsqrt, hpsp]
      calc c.angle B.family.metric lambda x t ^ 2 * c.projection.curvature B.family.metric x t *
            (c.horizontalSpeedFraction B.family.metric lambda x t *
              c.speed B.family.metric lambda x t)
          = (c.angle B.family.metric lambda x t ^ 2 *
              c.projection.curvature B.family.metric x t *
              c.horizontalSpeedFraction B.family.metric lambda x t) *
              c.speed B.family.metric lambda x t := by ring
        _ ≤ (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.curvature B.family.metric lambda x t) *
              c.speed B.family.metric lambda x t :=
            mul_le_mul_of_nonneg_right hfin (c.speed_nonneg B.family.metric lambda x t)
        _ = eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
              (c.curvature B.family.metric lambda x t *
                c.speed B.family.metric lambda x t) := by ring
    have hint : _root_.MeasureTheory.IntegrableOn (fun x => c.curvature B.family.metric lambda x t *
        c.speed B.family.metric lambda x t) (_root_.Set.Ioc (0 : ℝ) 1) volume :=
      (ProductCurve.curvature_mul_speed_integrable c B.family.metric lambda hlambda
        hc hi t ht).1
    have hintC : _root_.MeasureTheory.Integrable (fun x => eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
        (c.curvature B.family.metric lambda x t * c.speed B.family.metric lambda x t))
        (volume.restrict (_root_.Set.Ioc (0 : ℝ) 1)) := hint.const_mul _
    have hnn : 0 ≤ᵐ[volume.restrict (_root_.Set.Ioc (0 : ℝ) 1)]
        (fun x => Real.sqrt (c.projection.normSq B.family.metric
          (c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v)) x t) *
          c.projection.speed B.family.metric x t) :=
      _root_.MeasureTheory.ae_of_all _ (fun x => mul_nonneg (Real.sqrt_nonneg _)
        (c.projection.speed_nonneg B.family.metric x t))
    have hle := MeasureTheory.integral_mono_of_nonneg hnn hintC (_root_.MeasureTheory.ae_of_all _ hpoint)
    rw [MeasureTheory.integral_const_mul] at hle
    simpa only [CurveMap.areaError, CurveMap.integral, ProductCurve.totalCurvature,
      ProductCurve.integral,
      intervalIntegral.integral_of_le zero_le_one] using hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp

omit [SigmaCompactSpace M] hCompact hNonempty hBoundary in
theorem rfs_csf_swept_annulus (B : RicciBackground (I := I) (M := M) D a b)
    (hslope : curveShorteningLeastAreaSlope (I := I) (M := M) B)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hcont : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (_root_.Set.Icc a b))
    (s t : ℝ) (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc s b) :
    loopFamilyLeastArea B.family.metric γ t ≤ Real.exp (2 * B.B₀ * (t - s)) *
      (loopFamilyLeastArea B.family.metric γ s +
        ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) := by
  have hst : s ≤ t := ht.1
  have hsub : _root_.Set.Icc s t ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc hs.1 ht.2
  have hS := continuousOn_sweptDensity B γ hγ
  have hS' : ContinuousOn (fun v => (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v)
      (_root_.Set.Icc s t) := hS.mono hsub
  have hDini : ∀ v ∈ _root_.Set.Ico s t, v ∉ (∅ : Finset ℝ) → ∀ ε > 0, ∃ δ > 0,
      ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ, v + h ≤ t →
        (loopFamilyLeastArea B.family.metric γ (v + h) -
            loopFamilyLeastArea B.family.metric γ v) / h ≤
          -(-(2 * B.B₀)) * loopFamilyLeastArea B.family.metric γ v +
            (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v + ε := by
    intro v hv _ ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hslope γ hγ hcont v
      ⟨le_trans hs.1 hv.1, lt_of_lt_of_le hv.2 ht.2⟩ ε hε
    exact ⟨δ, hδpos, fun h hh hb => by
      simpa only [neg_mul, neg_neg] using hδ h hh (le_trans hb ht.2)⟩
  have hmain := rfs_csf_area_comparison_ode
    (fun x => loopFamilyLeastArea B.family.metric γ x)
    (fun _ : ℝ => -(2 * B.B₀))
    (fun v => (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v)
    s t hst (hcont.mono hsub) continuousOn_const hS' ∅ hDini
  have hInt : (∫ w in s..t, (-(2 * B.B₀) : ℝ)) = -(2 * B.B₀) * (t - s) := by
    rw [intervalIntegral.integral_const]
    ring
  have hIntv : ∀ v : ℝ, (∫ w in s..v, (-(2 * B.B₀) : ℝ)) = -(2 * B.B₀) * (v - s) := by
    intro v
    rw [intervalIntegral.integral_const]
    ring
  have hcongr : (∫ v in s..t, Real.exp (∫ w in s..v, (-(2 * B.B₀) : ℝ)) *
        (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) =
      ∫ v in s..t, Real.exp (-(2 * B.B₀) * (v - s)) *
        (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [hIntv v]
  rw [hInt, hcongr] at hmain
  have hExpMul : ∀ x : ℝ,
      Real.exp (2 * B.B₀ * (t - s)) * (Real.exp (-(2 * B.B₀) * (t - s)) * x) = x := by
    intro x
    rw [← mul_assoc, ← Real.exp_add]
    have hzero : 2 * B.B₀ * (t - s) + -(2 * B.B₀) * (t - s) = 0 := by ring
    rw [hzero, Real.exp_zero, one_mul]
  have hstep1 : loopFamilyLeastArea B.family.metric γ t ≤
      Real.exp (2 * B.B₀ * (t - s)) *
        (loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..t, Real.exp (-(2 * B.B₀) * (v - s)) *
            (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) := by
    have hpos : 0 < Real.exp (2 * B.B₀ * (t - s)) := Real.exp_pos _
    have h := mul_le_mul_of_nonneg_left hmain hpos.le
    rwa [hExpMul] at h
  have hle1 : ∀ v ∈ _root_.Set.Icc s t,
      Real.exp (-(2 * B.B₀) * (v - s)) *
        (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v ≤
        (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v := by
    intro v hv
    have hexp_le : Real.exp (-(2 * B.B₀) * (v - s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hv0 : 0 ≤ v - s := sub_nonneg.mpr hv.1
      nlinarith [B.B₀_nonneg]
    have hnnv := CurveMap.sweptDensity_nonneg (c := curveOfLoopFamily γ) B.family.metric (_root_.Set.Icc a b) v
    calc Real.exp (-(2 * B.B₀) * (v - s)) *
          (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v
        ≤ 1 * (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v :=
          mul_le_mul_of_nonneg_right hexp_le hnnv
      _ = (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v := one_mul _
  have hint1 : IntervalIntegrable (fun v => Real.exp (-(2 * B.B₀) * (v - s)) *
      (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) _root_.MeasureTheory.MeasureSpace.volume s t :=
    (((Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul
        hS')).intervalIntegrable_of_Icc hst
  have hint2 : IntervalIntegrable
      (fun v => (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) _root_.MeasureTheory.MeasureSpace.volume s t :=
    hS'.intervalIntegrable_of_Icc hst
  have hfinal : (∫ v in s..t, Real.exp (-(2 * B.B₀) * (v - s)) *
        (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) ≤
      ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v :=
    intervalIntegral.integral_mono_on hst hint1 hint2 hle1
  have hstep2 : Real.exp (2 * B.B₀ * (t - s)) *
        (loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..t, Real.exp (-(2 * B.B₀) * (v - s)) *
            (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) ≤
      Real.exp (2 * B.B₀ * (t - s)) *
        (loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) v) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact add_le_add le_rfl hfinal
  exact hstep1.trans hstep2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_swept_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_swept_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_swept_annulus ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_swept_annulus

omit hT2 hCompact hNonempty hBoundary in
theorem exp_increment_le (k h delta : ℝ) (hk : 0 ≤ k) (hh : 0 ≤ h) (hdelta : h ≤ delta) :
    Real.exp (k * h) - 1 ≤ k * Real.exp (k * delta) * h := by
  have htan := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(k * h)))
    (Real.exp_pos (k * h)).le
  have hexp : Real.exp (-(k * h)) * Real.exp (k * h) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hexp] at htan
  have hmono : Real.exp (k * h) ≤ Real.exp (k * delta) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdelta hk)
  have hmul := mul_le_mul_of_nonneg_left hmono (mul_nonneg hk hh)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exp_increment_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exp_increment_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exp_increment_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exp_increment_le

theorem rfs_csf_projected_ramp_pointwise (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : _root_.Set.Icc s v ⊆ _root_.Set.Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (_root_.Set.Icc s v)) :
    ∀ x t, t ∈ _root_.Set.Icc s v →
      0 < c.horizontalSpeedFraction B.family.metric lambda x t ∧
      (c.unitTangent B.family.metric lambda x t).1 =
        c.horizontalSpeedFraction B.family.metric lambda x t •
          c.projection.unitTangent B.family.metric x t ∧
      c.projection.speed B.family.metric x t =
        c.horizontalSpeedFraction B.family.metric lambda x t * c.speed B.family.metric lambda x t ∧
      c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v) x t =
        -(c.angle B.family.metric lambda x t ^ 2) • c.projection.curvatureVector B.family.metric x t ∧
      c.horizontalSpeedFraction B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t ≤ c.curvature B.family.metric lambda x t := by
  intro x t ht
  let _ := hsv
  let _ := hwindow
  let _ := hCompact
  let _ := hNonempty
  refine ⟨ProductCurve.horizontalSpeedFraction_pos c B.family.metric lambda hlambda hi x t ht,
    ProductCurve.unitTangent_fst_eq c B.family.metric lambda hlambda hi x t ht,
    ProductCurve.projection_speed_eq c B.family.metric lambda hlambda hi x t ht, ?_, ?_⟩
  · exact ProductCurve.projection_normalVelocityError c B.family.metric lambda hlambda hc hi x t ht
  · exact ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le c B.family.metric
      lambda hlambda hc hi x t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp_pointwise ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_projected_ramp_pointwise

theorem projected_normalVelocityError_norm (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : _root_.Set.Icc s v ⊆ _root_.Set.Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (_root_.Set.Icc s v)) (x t : ℝ) (ht : t ∈ _root_.Set.Icc s v) :
    Real.sqrt (c.projection.normSq B.family.metric
      (c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v)) x t) =
        c.angle B.family.metric lambda x t ^ 2 * c.projection.curvature B.family.metric x t := by
  have hz := (rfs_csf_projected_ramp_pointwise B lambda hlambda hsv hwindow c hc hi x t ht).2.2.2.1
  have hn : c.projection.normSq B.family.metric
      (c.projection.normalVelocityError B.family.metric (_root_.Set.Icc s v)) x t =
        (c.angle B.family.metric lambda x t ^ 2)^2 * c.projection.curvatureSq B.family.metric x t := by
    dsimp only [CurveMap.normSq, CurveMap.curvatureSq]
    rw [hz]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hn, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_normalVelocityError_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_normalVelocityError_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_normalVelocityError_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_normalVelocityError_norm

theorem projected_areaError_eq (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : _root_.Set.Icc s v ⊆ _root_.Set.Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (_root_.Set.Icc s v)) (t : ℝ) (ht : t ∈ _root_.Set.Icc s v) :
    c.projection.areaError B.family.metric (_root_.Set.Icc s v) t =
      ∫ x in (0 : ℝ)..1, c.angle B.family.metric lambda x t ^ 2 *
        c.projection.curvature B.family.metric x t * c.projection.speed B.family.metric x t := by
  unfold CurveMap.areaError CurveMap.integral
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [projected_normalVelocityError_norm B lambda hlambda hsv hwindow c hc hi x t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_areaError_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_areaError_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_areaError_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.projected_areaError_eq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
