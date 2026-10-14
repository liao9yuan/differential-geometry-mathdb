import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CurvatureProfiles
import Submission.DifferentialGeometry.Geometry.Curvature.RadialPositive

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.InnerProductSpace _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

theorem deriv_angle_pos {r : ℝ} (hr : r < transitionEnd) : 0 < deriv angle r := by
  rw [deriv_angle]
  exact mul_pos (by positivity) (Real.smoothTransition.pos_of_pos (sub_pos.mpr hr))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_pos

theorem deriv_deriv_warpingFunction_neg {r : ℝ} (hr : 0 < r) (hL : r < transitionEnd) :
    deriv (deriv warpingFunction) r < 0 := by
  rw [deriv_deriv_warpingFunction]
  apply mul_neg_of_pos_of_neg (by positivity)
  have hcos : 0 ≤ Real.cos (angle r) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg hr.le, Real.pi_pos],
      angle_le_pi_div_two r⟩
  have hsin : 0 < Real.sin (angle r) :=
    Real.sin_pos_of_pos_of_lt_pi (angle_pos hr)
      ((angle_le_pi_div_two r).trans_lt (half_lt_self Real.pi_pos))
  exact sub_neg.mpr ((mul_nonpos_of_nonneg_of_nonpos hcos
    (deriv_deriv_angle_nonpos r)).trans_lt (mul_pos hsin (sq_pos_of_pos (deriv_angle_pos hL))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_neg

theorem abs_deriv_warpingFunction_lt_one {r : ℝ} (hr : 0 < r) :
    |deriv warpingFunction r| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have ha := sq_pos_of_pos (warpingFunction_pos hr)
  linarith [deriv_warpingFunction_sq_add_half_sq_le_one r]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.abs_deriv_warpingFunction_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.abs_deriv_warpingFunction_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.abs_deriv_warpingFunction_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.abs_deriv_warpingFunction_lt_one

theorem radialSectionalValue_pos {r : ℝ} (hr : r < transitionEnd) :
    0 < radialSectionalValue r := by
  by_cases h0 : r ≤ 0
  · norm_num [radialSectionalValue, h0]
  · have hp : 0 < r := lt_of_not_ge h0
    rw [radialSectionalValue_of_pos hp]
    exact div_pos (neg_pos.mpr (deriv_deriv_warpingFunction_neg hp hr)) (warpingFunction_pos hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_pos

theorem sectionalCurvature_radial_pos {x v : E3} (hx : x ≠ 0)
    (hL : ‖x‖ < transitionEnd) (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    0 < sectionalCurvature metric x x v := by
  rw [sectionalCurvature_radial_eq_profile hx hv hxv]
  exact radialSectionalValue_pos hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_pos

theorem metricRm04_pos {x : E3} (hL : ‖x‖ < transitionEnd) (u v : E3)
    (hplane : 0 < metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2) :
    0 < metricRm04StandardAt metric x u v v u := by
  by_cases hx : x = 0
  · subst x
    rw [metricRm04_zero]
    apply mul_pos (by norm_num)
    simpa only [metric_inner_zero] using hplane
  · exact metricRm04StdAt_radialBilinearField_pos metric (metric_eventually_radial hx)
      contDiff_warpingFunction hx (warpingFunction_pos (norm_pos_iff.mpr hx))
      (deriv_deriv_warpingFunction_neg (norm_pos_iff.mpr hx) hL)
      (abs_deriv_warpingFunction_lt_one (norm_pos_iff.mpr hx)) u v hplane

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricRm04_pos

theorem sectionalCurvature_pos {x : E3} (hL : ‖x‖ < transitionEnd) (u v : E3)
    (hplane : metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2 ≠ 0) :
    0 < sectionalCurvature metric x u v := by
  have hpos : 0 < metric.inner x u u * metric.inner x v v - (metric.inner x u v) ^ 2 :=
    (sectionalCurvatureDenominator_nonneg metric x u v).lt_of_ne' hplane
  exact (div_pos (metricRm04_pos hL u v hpos) hpos).trans_eq
    (sectionalCurvature_eq_metricRm04StandardAt_div metric x u v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_pos

end DifferentialGeometry.PDE.RicciFlow.StandardCap
