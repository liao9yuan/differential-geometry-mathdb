import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Toponogov

variable {X : Type*} [MetricSpace X] {ι : Type*} {z : X}
  {L : ι → ℝ} {gamma : ι → ℝ → X}

theorem dist_le_sqrt_limitingRadialAngle
    (hrad : IsRadialFamily z L gamma) {i j : ι} {s t : ℝ}
    (hs : s ∈ _root_.Set.Ioc 0 (L i)) (ht : t ∈ _root_.Set.Ioc 0 (L j)) :
    _root_.Dist.dist (gamma i s) (gamma j t) ≤
      Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (limitingRadialAngle L gamma i j)) := by
  have hsides := radialComparisonAngle_sideInequalities hrad hs ht
  have hangle : radialComparisonAngle gamma i j s t ≤ limitingRadialAngle L gamma i j :=
    le_csSup (positiveRectangleValues_radial_bddAbove L gamma i j) ⟨s, hs, t, ht, rfl⟩
  have hsq := sq_le_cos_of_comparisonAngle_le hs.1 ht.1 hsides.1 hsides.2
    (limitingRadialAngle_mem_Icc gamma (hs.1.trans_le hs.2) (ht.1.trans_le ht.2)).2 hangle
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_le_sqrt hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.dist_le_sqrt_limitingRadialAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.dist_le_sqrt_limitingRadialAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.dist_le_sqrt_limitingRadialAngle ``Submission.DifferentialGeometry.Toponogov.dist_le_sqrt_limitingRadialAngle

private theorem tendsto_mul_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ => s * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : _root_.Filter.Tendsto (fun s : ℝ => s * a) (𝓝 (0 : ℝ)) (𝓝 (0 * a)) :=
      (continuous_id.mul_const a).continuousAt
    simpa only [_root_.MulZeroClass.zero_mul] using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_pos hs ha

run_cmd do
  let target := ``Submission.DifferentialGeometry.Toponogov.tendsto_mul_nhdsGT_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Toponogov.tendsto_mul_nhdsGT_zero target :: scope.openDecls } }

theorem tendsto_rescaled_radial_distance
    (hrad : IsRadialFamily z L gamma) {i j : ι}
    (hLi : 0 < L i) (hLj : 0 < L j)
    (hmono : CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    _root_.Filter.Tendsto (fun rho : ℝ => _root_.Dist.dist (gamma i (rho * a)) (gamma j (rho * b)) / rho)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (limitingRadialAngle L gamma i j)))) := by
  have harg : _root_.Filter.Tendsto (fun rho : ℝ => (rho * a, rho * b))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) :=
    (tendsto_mul_nhdsGT_zero ha).prodMk (tendsto_mul_nhdsGT_zero hb)
  have hangle := (tendsto_limitingRadialAngle gamma hLi hLj hmono).comp harg
  have hmodel : _root_.Filter.Tendsto (fun rho : ℝ => Real.sqrt
      (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (radialComparisonAngle gamma i j (rho * a) (rho * b))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (limitingRadialAngle L gamma i j)))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub ((Real.continuous_cos.continuousAt.tendsto.comp hangle).const_mul (2 * a * b)))
  apply hmodel.congr'
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_mul_nhdsGT_zero ha).eventually (Ioc_mem_nhdsGT hLi),
    (tendsto_mul_nhdsGT_zero hb).eventually (Ioc_mem_nhdsGT hLj)] with rho hrho hsa htb
  have hr : 0 < rho := hrho
  have hsides := radialComparisonAngle_sideInequalities hrad hsa htb
  have hc := cos_comparisonAngle hsa.1 htb.1 hsides.1 hsides.2
  change Real.cos (radialComparisonAngle gamma i j (rho * a) (rho * b)) =
    ((rho * a) ^ 2 + (rho * b) ^ 2 - _root_.Dist.dist (gamma i (rho * a)) (gamma j (rho * b)) ^ 2) /
      (2 * (rho * a) * (rho * b)) at hc
  have heq : a ^ 2 + b ^ 2 - 2 * a * b *
      Real.cos (radialComparisonAngle gamma i j (rho * a) (rho * b)) =
      (_root_.Dist.dist (gamma i (rho * a)) (gamma j (rho * b)) / rho) ^ 2 := by
    rw [hc]
    field_simp [ha.ne', hb.ne', hr.ne']
    ring
  rw [heq, Real.sqrt_sq (div_nonneg dist_nonneg hr.le)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.tendsto_rescaled_radial_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.tendsto_rescaled_radial_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.tendsto_rescaled_radial_distance ``Submission.DifferentialGeometry.Toponogov.tendsto_rescaled_radial_distance

private theorem min_mul_div_le_of_comparisonAngle_le
    {L a b d D : ℝ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 ≤ d) (hdL : d ≤ L + L) (hD : |a - b| ≤ D) (hDab : D ≤ a + b)
    (hangle : comparisonAngle L L d ≤ comparisonAngle a b D) :
    min a b * (d / L) ≤ D := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngle_mem_Icc L L d).1 (comparisonAngle_mem_Icc a b D).2 hangle
  rw [cos_comparisonAngle hL hL (by simpa using hd) hdL,
    cos_comparisonAngle ha hb hD hDab, comparisonCosine, comparisonCosine,
    div_le_div_iff₀ (by positivity : 0 < 2 * a * b) (by positivity : 0 < 2 * L * L)] at hcos
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hm : 0 ≤ _root_.Min.min a b := (lt_min ha hb).le
  have hmin : (_root_.Min.min a b) ^ 2 ≤ a * b := by
    rw [pow_two]
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm ha.le
  have hmul := mul_le_mul_of_nonneg_left hmin (sq_nonneg d)
  have hsq : (_root_.Min.min a b * d) ^ 2 ≤ (D * L) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (a - b)) (sq_nonneg L)]
  have hle := (sq_le_sq₀ (mul_nonneg hm hd) (mul_nonneg hD0 hL.le)).mp hsq
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hL).mpr hle

run_cmd do
  let target := ``Submission.DifferentialGeometry.Toponogov.min_mul_div_le_of_comparisonAngle_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Toponogov.min_mul_div_le_of_comparisonAngle_le target :: scope.openDecls } }

theorem min_mul_dist_div_le_dist_of_radialComparisonAngle_nonincreasing
    {r : ℝ} (hr : 0 < r) (hrad : IsRadialFamily z (fun _ : ι => r) gamma)
    {i j : ι}
    (hmono : CoordinatewiseNonincreasingOn r r (radialComparisonAngle gamma i j))
    {s t : ℝ} (hs : s ∈ _root_.Set.Ioc 0 r) (ht : t ∈ _root_.Set.Ioc 0 r) :
    min s t * (_root_.Dist.dist (gamma i r) (gamma j r) / r) ≤ _root_.Dist.dist (gamma i s) (gamma j t) := by
  have hbig := radialComparisonAngle_sideInequalities hrad
    (i := i) (j := j) (show r ∈ _root_.Set.Ioc 0 r from ⟨hr, le_rfl⟩) ⟨hr, le_rfl⟩
  have hsmall := radialComparisonAngle_sideInequalities hrad (i := i) (j := j) hs ht
  have hangle : radialComparisonAngle gamma i j r r ≤ radialComparisonAngle gamma i j s t :=
    ((hmono.2 ⟨hr, le_rfl⟩ ht ⟨hr, le_rfl⟩ ht.2).trans
      (hmono.1 hs ⟨hr, le_rfl⟩ ht hs.2))
  exact min_mul_div_le_of_comparisonAngle_le hr hs.1 ht.1 dist_nonneg hbig.2
    hsmall.1 hsmall.2 hangle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.min_mul_dist_div_le_dist_of_radialComparisonAngle_nonincreasing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.min_mul_dist_div_le_dist_of_radialComparisonAngle_nonincreasing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.min_mul_dist_div_le_dist_of_radialComparisonAngle_nonincreasing ``Submission.DifferentialGeometry.Toponogov.min_mul_dist_div_le_dist_of_radialComparisonAngle_nonincreasing

theorem dist_le_mul_limitingRadialAngle
    (hrad : IsRadialFamily z L gamma) {i j : ι} {s : ℝ}
    (hsi : s ∈ _root_.Set.Ioc 0 (L i)) (hsj : s ∈ _root_.Set.Ioc 0 (L j)) :
    dist (gamma i s) (gamma j s) ≤ s * limitingRadialAngle L gamma i j := by
  let theta := limitingRadialAngle L gamma i j
  have htheta := limitingRadialAngle_mem_Icc gamma
    (hsi.1.trans_le hsi.2) (hsj.1.trans_le hsj.2)
  have hsin : 0 ≤ Real.sin (theta / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [htheta.1])
      (by linarith [htheta.2, Real.pi_pos])
  have hcos : Real.cos theta = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
    rw [show theta = 2 * (theta / 2) by ring, Real.cos_two_mul_eq_one_sub]
    ring_nf
  have hsq : s ^ 2 + s ^ 2 - 2 * s * s * Real.cos theta =
      (2 * s * Real.sin (theta / 2)) ^ 2 := by rw [hcos]; ring
  have hh := dist_le_sqrt_limitingRadialAngle hrad hsi hsj
  change _root_.Dist.dist (gamma i s) (gamma j s) ≤ Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * Real.cos theta) at hh
  rw [hsq, Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) hsi.1.le) hsin)] at hh
  have hsinle := Real.sin_le (show 0 ≤ theta / 2 by linarith [htheta.1])
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hsinle hsi.1.le])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.dist_le_mul_limitingRadialAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.dist_le_mul_limitingRadialAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.dist_le_mul_limitingRadialAngle ``Submission.DifferentialGeometry.Toponogov.dist_le_mul_limitingRadialAngle

end DifferentialGeometry.Toponogov
