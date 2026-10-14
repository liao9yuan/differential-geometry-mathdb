import Submission.DifferentialGeometry.Topology.LoopSpace.RadialExtension
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.ContinuousLinearMap
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def radialCone (p : F) (b : Circle → F) (z : ℂ) : F :=
  p + ‖z‖ • (b (radialDirection z) - p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialCone ``Submission.DifferentialGeometry.Topology.radialCone

@[simp] theorem radialCone_zero (p : F) (b : Circle → F) : radialCone p b 0 = p := by
  simp [radialCone]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialCone_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialCone_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialCone_zero ``Submission.DifferentialGeometry.Topology.radialCone_zero

theorem radialCone_circle (p : F) (b : Circle → F) (z : Circle) :
    radialCone p b (z : ℂ) = b z := by
  simp only [radialCone, Circle.norm_coe, one_smul, radialDirection_unit, add_sub_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialCone_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialCone_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialCone_circle ``Submission.DifferentialGeometry.Topology.radialCone_circle

theorem radialCone_lipschitz {p : F} {b : Circle → F} {K D : ℝ≥0}
    (hb : LipschitzWith K b) (hD : ∀ z, ‖b z - p‖ ≤ D) :
    LipschitzWith (2 * K + D) (radialCone p b) := by
  have hordered (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖) :
      dist (radialCone p b x) (radialCone p b y) ≤ (2 * (K : ℝ) + D) * _root_.Dist.dist x y := by
    by_cases hx : x = 0
    · subst x
      rw [radialCone_zero, radialCone, dist_self_add_right, norm_smul, norm_norm, dist_zero_left]
      nlinarith [hD (radialDirection y), K.coe_nonneg, norm_nonneg y]
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : y ≠ 0 := norm_pos_iff.mp (hx0.trans_le hxy)
    have hdir : _root_.Dist.dist (radialDirection x) (radialDirection y) ≤ (2 / ‖x‖) * _root_.Dist.dist x y := by
      change _root_.Dist.dist (radialDirection x : ℂ) (radialDirection y : ℂ) ≤ _
      rw [radialDirection_coe hx, radialDirection_coe hy]
      exact DifferentialGeometry.Analysis.normalize_dist_le hx0 le_rfl hxy
    have hang := (hb.dist_le_mul (radialDirection x) (radialDirection y)).trans
      (mul_le_mul_of_nonneg_left hdir K.coe_nonneg)
    have heq : radialCone p b x - radialCone p b y =
        ‖x‖ • (b (radialDirection x) - b (radialDirection y)) +
          (‖x‖ - ‖y‖) • (b (radialDirection y) - p) := by
      simp only [radialCone, smul_sub, sub_smul]
      abel
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖‖x‖ • (b (radialDirection x) - b (radialDirection y))‖ +
          ‖(‖x‖ - ‖y‖) • (b (radialDirection y) - p)‖ := norm_add_le _ _
      _ ≤ ‖x‖ * _root_.Dist.dist (b (radialDirection x)) (b (radialDirection y)) +
          |‖x‖ - ‖y‖| * D := by
        rw [norm_smul, norm_norm, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _))
      _ ≤ ‖x‖ * ((K : ℝ) * ((2 / ‖x‖) * _root_.Dist.dist x y)) + _root_.Dist.dist x y * D := by
        exact add_le_add (mul_le_mul_of_nonneg_left hang hx0.le)
          (mul_le_mul_of_nonneg_right
            (show |‖x‖ - ‖y‖| ≤ _root_.Dist.dist x y from by
              simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y) D.coe_nonneg)
      _ = _ := by field_simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change _root_.Dist.dist (radialCone p b x) (radialCone p b y) ≤ (2 * (K : ℝ) + D) * _root_.Dist.dist x y
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · exact hordered x y hxy
  · simpa only [dist_comm] using hordered y x hyx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialCone_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialCone_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialCone_lipschitz ``Submission.DifferentialGeometry.Topology.radialCone_lipschitz

def periodicCircleMap {a : ℝ → F} (ha : Function.Periodic a 1) (z : Circle) : F :=
  ha.lift ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z +
    ((1 / 2 : ℝ) : loopCircle))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicCircleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicCircleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicCircleMap ``Submission.DifferentialGeometry.Topology.periodicCircleMap

def periodicLoopCone (p : F) {a : ℝ → F} (ha : Function.Periodic a 1) : ℂ → F :=
  radialCone p (periodicCircleMap ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicLoopCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicLoopCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicLoopCone ``Submission.DifferentialGeometry.Topology.periodicLoopCone

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem periodicCircleMap_circleMap {a : ℝ → F} (ha : Function.Periodic a 1) (t : ℝ) :
    periodicCircleMap ha
      ⟨circleMap 0 1 (2 * Real.pi * t - Real.pi), by
        apply mem_sphere_zero_iff_norm.mpr
        simp only [norm_circleMap_zero, abs_one]⟩ = a t := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : e (((t - 1 / 2 : ℝ) : loopCircle)) =
      ⟨circleMap 0 1 (2 * Real.pi * t - Real.pi), by
        apply mem_sphere_zero_iff_norm.mpr
        simp only [norm_circleMap_zero, abs_one]⟩ := by
    apply Subtype.ext
    simp only [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
      Circle.coe_exp, div_one, circleMap, Complex.ofReal_one, one_mul, zero_add]
    congr 1
    push_cast
    ring
  change ha.lift (e.symm _ + ((1 / 2 : ℝ) : loopCircle)) = a t
  rw [← he, e.symm_apply_apply, ← AddCircle.coe_add]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicCircleMap_circleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicCircleMap_circleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicCircleMap_circleMap ``Submission.DifferentialGeometry.Topology.periodicCircleMap_circleMap

omit [NormedSpace ℝ F] in
theorem periodicCircleMap_lipschitz {a : ℝ → F} {K : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith K a) :
    LipschitzWith K (periodicCircleMap ha) := by
  have hlift : LipschitzWith K (ha.lift : loopCircle → F) := by
    apply loop_lipschitz_of_lift
    simpa only [Function.Periodic.lift_coe] using hLip
  have hshift : LipschitzWith 1 (fun x : loopCircle => x + ((1 / 2 : ℝ) : loopCircle)) :=
    (isometry_add_right ((1 / 2 : ℝ) : loopCircle)).lipschitz
  change LipschitzWith K (ha.lift ∘
    (fun x : loopCircle => x + ((1 / 2 : ℝ) : loopCircle)) ∘
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm)
  simpa only [mul_one] using hlift.comp (hshift.comp circle_parameter_lipschitz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicCircleMap_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicCircleMap_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicCircleMap_lipschitz ``Submission.DifferentialGeometry.Topology.periodicCircleMap_lipschitz

theorem periodicLoopCone_boundary (p : F) {a : ℝ → F} (ha : Function.Periodic a 1) (t : ℝ) :
    periodicLoopCone p ha (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = a t := by
  exact (radialCone_circle p (periodicCircleMap ha)
    ⟨circleMap 0 1 (2 * Real.pi * t - Real.pi), by
        apply mem_sphere_zero_iff_norm.mpr
        simp only [norm_circleMap_zero, abs_one]⟩).trans
      (periodicCircleMap_circleMap ha t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicLoopCone_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicLoopCone_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicLoopCone_boundary ``Submission.DifferentialGeometry.Topology.periodicLoopCone_boundary

theorem exists_lipschitzWith_periodicLoopCone
    (p : F) {a : ℝ → F} {K : ℝ≥0} (ha : Function.Periodic a 1) (hLip : LipschitzWith K a) :
    ∃ C : ℝ≥0, LipschitzWith C (periodicLoopCone p ha) := by
  have hb := periodicCircleMap_lipschitz ha hLip
  obtain ⟨D, hD⟩ := (isCompact_range (hb.continuous.sub continuous_const)).isBounded.exists_norm_le
  refine ⟨2 * K + Real.toNNReal D, radialCone_lipschitz hb (fun z => ?_)⟩
  exact (hD _ (_root_.Set.mem_range_self z)).trans (Real.le_coe_toNNReal D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_lipschitzWith_periodicLoopCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_lipschitzWith_periodicLoopCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_lipschitzWith_periodicLoopCone ``Submission.DifferentialGeometry.Topology.exists_lipschitzWith_periodicLoopCone

theorem periodicLoopCone_normalized_polar
    (p : F) {a : ℝ → F} (ha : Function.Periodic a 1) {q : ℝ × ℝ} (hq : 0 < q.1) :
    periodicLoopCone p ha
      (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi)) =
        p + q.1 • (a q.2 - p) := by
  let c : Circle :=
    ⟨circleMap 0 1 (2 * Real.pi * q.2 - Real.pi), by
        apply mem_sphere_zero_iff_norm.mpr
        simp only [norm_circleMap_zero, abs_one]⟩
  have hpolar : Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi) = q.1 • (c : ℂ) := by
    change Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi) =
      q.1 • circleMap 0 1 (2 * Real.pi * q.2 - Real.pi)
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.ofReal_one, one_mul, zero_add]
    rw [Complex.exp_mul_I]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_cos, Complex.ofReal_sin, Complex.real_smul]
  rw [hpolar]
  simp only [periodicLoopCone, radialCone, norm_smul, Real.norm_eq_abs, abs_of_pos hq,
    Circle.norm_coe, mul_one, radialDirection_pos_smul hq]
  rw [periodicCircleMap_circleMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicLoopCone_normalized_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicLoopCone_normalized_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicLoopCone_normalized_polar ``Submission.DifferentialGeometry.Topology.periodicLoopCone_normalized_polar

private theorem fderiv_cone_profile (p : F) {a : ℝ → F} {q : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a q.2) :
    fderiv ℝ (fun z : ℝ × ℝ => p + z.1 • (a z.2 - p)) q =
      q.1 • ((fderiv ℝ a q.2).comp (_root_.ContinuousLinearMap.snd ℝ ℝ ℝ)) + (_root_.ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (a q.2 - p) := by
  simpa using ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).smul
    ((ha.hasFDerivAt.comp q hasFDerivAt_snd).sub_const p)).const_add p |>.fderiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fderiv_cone_profile
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fderiv_cone_profile target :: scope.openDecls } }

theorem fderiv_periodicLoopCone_normalized_polar
    (p : F) {a : ℝ → F} (ha : Function.Periodic a 1) {q : ℝ × ℝ}
    (hq : 0 < q.1) (had : DifferentiableAt ℝ a q.2) :
    (fderiv ℝ (fun z : ℝ × ℝ => periodicLoopCone p ha
      (Complex.polarCoord.symm (z.1, 2 * Real.pi * z.2 - Real.pi))) q (1, 0) = a q.2 - p) ∧
    (fderiv ℝ (fun z : ℝ × ℝ => periodicLoopCone p ha
      (Complex.polarCoord.symm (z.1, 2 * Real.pi * z.2 - Real.pi))) q (0, 1) =
        q.1 • deriv a q.2) := by
  have heq : (fun z : ℝ × ℝ => periodicLoopCone p ha
      (Complex.polarCoord.symm (z.1, 2 * Real.pi * z.2 - Real.pi))) =ᶠ[𝓝 q]
        (fun z => p + z.1 • (a z.2 - p)) := by
    filter_upwards [(continuous_fst.tendsto q) (Ioi_mem_nhds hq)] with z hz
    exact periodicLoopCone_normalized_polar p ha hz
  rw [heq.fderiv_eq, fderiv_cone_profile p had]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fderiv_periodicLoopCone_normalized_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fderiv_periodicLoopCone_normalized_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fderiv_periodicLoopCone_normalized_polar ``Submission.DifferentialGeometry.Topology.fderiv_periodicLoopCone_normalized_polar

end DifferentialGeometry.Topology

end
