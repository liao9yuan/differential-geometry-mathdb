import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Mathlib.Analysis.InnerProductSpace.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis

open _root_.Set
open scoped _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E]

def ballCutoffArgument (center : E) (r R : ℝ) (x : E) : ℝ :=
  1 + (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffArgument then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffArgument"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffArgument ``Submission.DifferentialGeometry.Analysis.ballCutoffArgument

def ballCutoff (center : E) (r R : ℝ) (x : E) : ℝ :=
  CutoffProfile.value (ballCutoffArgument center r R x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff ``Submission.DifferentialGeometry.Analysis.ballCutoff

def ballCutoffArgumentFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (R ^ 2 - r ^ 2)⁻¹ • ((2 : ℕ) • innerSL ℝ (x - center))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv ``Submission.DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv

def ballCutoffArgumentFDeriv2 [InnerProductSpace ℝ E]
    (r R : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (R ^ 2 - r ^ 2)⁻¹ •
    ((2 : ℕ) • (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2 ``Submission.DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2

@[simp]
theorem ballCutoffArgumentFDeriv_apply [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x v : E) :
    ballCutoffArgumentFDeriv center r R x v =
      (R ^ 2 - r ^ 2)⁻¹ * (2 * _root_.Inner.inner ℝ (x - center) v) := by
  simp only [ballCutoffArgumentFDeriv, two_nsmul,
    add_apply, smul_apply,
    coe_innerSL_apply, inner_sub_left, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv_apply ``Submission.DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv_apply

@[simp]
theorem ballCutoffArgumentFDeriv2_apply [InnerProductSpace ℝ E]
    (r R : ℝ) (v w : E) :
    ballCutoffArgumentFDeriv2 (E := E) r R v w =
      (R ^ 2 - r ^ 2)⁻¹ * (2 * _root_.Inner.inner ℝ v w) := by
  unfold ballCutoffArgumentFDeriv2
  change ((((R ^ 2 - r ^ 2)⁻¹ •
    ((2 : ℕ) • (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ))) v) w) = _
  rw [smul_apply]
  have hn :
      (((2 : ℕ) • (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ)) v) =
        (2 : ℕ) • innerSL ℝ v := rfl
  rw [hn, smul_apply]
  have hn' : (((2 : ℕ) • innerSL ℝ v) w) =
      (2 : ℕ) • _root_.Inner.inner ℝ v w := rfl
  rw [hn', nsmul_eq_mul]
  simp only [smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2_apply ``Submission.DifferentialGeometry.Analysis.ballCutoffArgumentFDeriv2_apply

def ballCutoffFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  deriv CutoffProfile.value (ballCutoffArgument center r R x) •
    ballCutoffArgumentFDeriv center r R x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv

def ballCutoffFDeriv2 [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  deriv CutoffProfile.value (ballCutoffArgument center r R x) •
      ballCutoffArgumentFDeriv2 r R +
    (deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x) •
        ballCutoffArgumentFDeriv center r R x).smulRight
      (ballCutoffArgumentFDeriv center r R x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2 ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2

def ballCutoffFDerivBound (r R : ℝ) : ℝ :=
  CutoffProfile.derivBound * (2 * R / (R ^ 2 - r ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDerivBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDerivBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDerivBound ``Submission.DifferentialGeometry.Analysis.ballCutoffFDerivBound

def ballCutoffFDeriv2Bound (r R : ℝ) : ℝ :=
  CutoffProfile.derivBound *
    (2 / (R ^ 2 - r ^ 2) + (2 * R / (R ^ 2 - r ^ 2)) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound

theorem hasFDerivAt_ballCutoffArgument [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoffArgument center r R)
      (ballCutoffArgumentFDeriv center r R x) x := by
  have hnorm := ((hasFDerivAt_id x).sub_const center).norm_sq
  have h := (hnorm.sub_const (r ^ 2)).mul_const (R ^ 2 - r ^ 2)⁻¹
  have h' := (hasFDerivAt_const (x := x) (c := (1 : ℝ))).add h
  simpa [ballCutoffArgument, ballCutoffArgumentFDeriv] using! h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgument then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgument"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgument ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgument

theorem hasFDerivAt_ballCutoffArgumentFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoffArgumentFDeriv center r R)
      (ballCutoffArgumentFDeriv2 r R) x := by
  simpa [ballCutoffArgumentFDeriv, ballCutoffArgumentFDeriv2] using!
    (((R ^ 2 - r ^ 2)⁻¹ •
      ((2 : ℕ) • (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ))).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const center))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgumentFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgumentFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgumentFDeriv ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffArgumentFDeriv

theorem hasFDerivAt_ballCutoff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoff center r R)
      (ballCutoffFDeriv center r R x) x := by
  have hprofile : HasDerivAt CutoffProfile.value
      (deriv CutoffProfile.value (ballCutoffArgument center r R x))
      (ballCutoffArgument center r R x) :=
    (CutoffProfile.contDiff.differentiable (by simp)
      (ballCutoffArgument center r R x)).hasDerivAt
  simpa only [ballCutoff, ballCutoffFDeriv, Function.comp_def] using!
    hprofile.comp_hasFDerivAt x
      (hasFDerivAt_ballCutoffArgument center r R x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasFDerivAt_ballCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoff ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_ballCutoff

theorem hasFDerivAt_ballCutoffFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoffFDeriv center r R)
      (ballCutoffFDeriv2 center r R x) x := by
  have hle2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤
        (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    exact h
  have hprofile2 : HasDerivAt (deriv CutoffProfile.value)
      (deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x))
      (ballCutoffArgument center r R x) :=
    ((CutoffProfile.contDiff.of_le hle2).deriv' (n := 1)).differentiable
      (by simp) (ballCutoffArgument center r R x) |>.hasDerivAt
  have hcoefficient : HasFDerivAt
      (fun y ↦ deriv CutoffProfile.value (ballCutoffArgument center r R y))
      (deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x) •
        ballCutoffArgumentFDeriv center r R x) x := by
    simpa only [Function.comp_def] using
      hprofile2.comp_hasFDerivAt x
        (hasFDerivAt_ballCutoffArgument center r R x)
  simpa only [ballCutoffFDeriv, ballCutoffFDeriv2] using!
    hcoefficient.smul
      (hasFDerivAt_ballCutoffArgumentFDeriv center r R x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffFDeriv ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_ballCutoffFDeriv

theorem ballCutoffFDerivBound_nonneg
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffFDerivBound r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  exact mul_nonneg CutoffProfile.derivBound_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (hr.trans hrR.le)) hden.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDerivBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDerivBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDerivBound_nonneg ``Submission.DifferentialGeometry.Analysis.ballCutoffFDerivBound_nonneg

theorem ballCutoffFDeriv2Bound_nonneg
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffFDeriv2Bound r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  exact mul_nonneg CutoffProfile.derivBound_nonneg
    (add_nonneg (div_nonneg (by norm_num) hden.le) (sq_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound_nonneg ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound_nonneg

theorem norm_ballCutoffArgumentFDeriv_le
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {x : E}
    (hx : _root_.Dist.dist x center ≤ R) :
    ‖ballCutoffArgumentFDeriv center r R x‖ ≤
      2 * R / (R ^ 2 - r ^ 2) := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hdist : ‖x - center‖ ≤ R := by
    simpa [dist_eq_norm] using hx
  rw [ballCutoffArgumentFDeriv, norm_smul, RCLike.norm_nsmul ℝ,
    innerSL_apply_norm, nsmul_eq_mul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hden]
  rw [div_eq_mul_inv]
  nlinarith [inv_pos.mpr hden, norm_nonneg (x - center)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv_le ``Submission.DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv_le

theorem norm_ballCutoffArgumentFDeriv2_le
    [InnerProductSpace ℝ E] {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    ‖ballCutoffArgumentFDeriv2 (E := E) r R‖ ≤
      2 / (R ^ 2 - r ^ 2) := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  refine ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (by norm_num) hden.le) ?_
  intro v
  change ‖(R ^ 2 - r ^ 2)⁻¹ • ((2 : ℕ) • innerSL ℝ v)‖ ≤
    2 / (R ^ 2 - r ^ 2) * ‖v‖
  rw [norm_smul, RCLike.norm_nsmul ℝ, innerSL_apply_norm,
    nsmul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hden,
    div_eq_mul_inv]
  ring_nf
  exact le_refl ((R ^ 2 - r ^ 2)⁻¹ * ‖v‖ * (2 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv2_le ``Submission.DifferentialGeometry.Analysis.norm_ballCutoffArgumentFDeriv2_le

theorem two_le_ballCutoffArgument_of_le_dist
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) {x : E}
    (hx : R ≤ _root_.Dist.dist x center) :
    2 ≤ ballCutoffArgument center r R x := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hR : 0 ≤ R := hr.trans hrR.le
  have hdist : R ≤ ‖x - center‖ := by
    simpa [dist_eq_norm] using hx
  have hsq : R ^ 2 ≤ ‖x - center‖ ^ 2 :=
    (sq_le_sq₀ hR (norm_nonneg _)).2 hdist
  have hquot : 1 ≤
      (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) := by
    rw [le_div_iff₀ hden]
    linarith
  simp only [ballCutoffArgument]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_le_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_le_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_le_dist ``Submission.DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_le_dist

theorem two_le_ballCutoffArgument_of_not_le
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) {x : E}
    (hx : ¬dist x center ≤ R) :
    2 ≤ ballCutoffArgument center r R x :=
  two_le_ballCutoffArgument_of_le_dist hr hrR (not_le.mp hx).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_not_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_not_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_not_le ``Submission.DifferentialGeometry.Analysis.two_le_ballCutoffArgument_of_not_le

theorem ballCutoffFDeriv_eq_zero_of_le_dist
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {x : E} (hx : R ≤ _root_.Dist.dist x center) :
    ballCutoffFDeriv center r R x = 0 := by
  rw [ballCutoffFDeriv,
    CutoffProfile.deriv_zero_of_ge
      (two_le_ballCutoffArgument_of_le_dist hr hrR hx), zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_le_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_le_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_le_dist ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_le_dist

theorem ballCutoffFDeriv2_eq_zero_of_le_dist
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {x : E} (hx : R ≤ _root_.Dist.dist x center) :
    ballCutoffFDeriv2 center r R x = 0 := by
  have harg := two_le_ballCutoffArgument_of_le_dist hr hrR hx
  ext v w
  simp [ballCutoffFDeriv2, CutoffProfile.deriv_zero_of_ge harg,
    CutoffProfile.deriv2_zero_of_ge harg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_le_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_le_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_le_dist ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_le_dist

theorem ballCutoffFDeriv_eq_zero_of_not_mem_ball
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {x : E} (hx : x ∉ Metric.ball center R) :
    ballCutoffFDeriv center r R x = 0 :=
  ballCutoffFDeriv_eq_zero_of_le_dist hr hrR
    (by simpa [Metric.mem_ball, dist_comm] using hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_not_mem_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_not_mem_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_not_mem_ball ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv_eq_zero_of_not_mem_ball

theorem ballCutoffFDeriv2_eq_zero_of_not_mem_ball
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {x : E} (hx : x ∉ Metric.ball center R) :
    ballCutoffFDeriv2 center r R x = 0 :=
  ballCutoffFDeriv2_eq_zero_of_le_dist hr hrR
    (by simpa [Metric.mem_ball, dist_comm] using hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_not_mem_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_not_mem_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_not_mem_ball ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2_eq_zero_of_not_mem_ball

theorem norm_ballCutoffFDeriv_le
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (x : E) :
    ‖ballCutoffFDeriv center r R x‖ ≤ ballCutoffFDerivBound r R := by
  by_cases hx : _root_.Dist.dist x center ≤ R
  · rw [ballCutoffFDeriv, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul
      (CutoffProfile.abs_deriv_le_derivBound _)
      (norm_ballCutoffArgumentFDeriv_le hr hrR hx)
      (norm_nonneg _) CutoffProfile.derivBound_nonneg
  · have harg : 2 ≤ ballCutoffArgument center r R x := by
      have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
      have hR : 0 ≤ R := hr.trans hrR.le
      have hdist : R ≤ ‖x - center‖ := by
        simpa [dist_eq_norm] using (not_le.mp hx).le
      have hsq : R ^ 2 ≤ ‖x - center‖ ^ 2 :=
        (sq_le_sq₀ hR (norm_nonneg _)).2 hdist
      have hquot : 1 ≤
          (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith
      simp only [ballCutoffArgument]
      linarith
    rw [ballCutoffFDeriv, CutoffProfile.deriv_zero_of_ge harg, zero_smul,
      norm_zero]
    exact ballCutoffFDerivBound_nonneg hr hrR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_ballCutoffFDeriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_ballCutoffFDeriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_ballCutoffFDeriv_le ``Submission.DifferentialGeometry.Analysis.norm_ballCutoffFDeriv_le

theorem norm_ballCutoffFDeriv2_le
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (x : E) :
    ‖ballCutoffFDeriv2 center r R x‖ ≤ ballCutoffFDeriv2Bound r R := by
  by_cases hx : _root_.Dist.dist x center ≤ R
  · let d1 := ballCutoffArgumentFDeriv center r R x
    let d2 := ballCutoffArgumentFDeriv2 (E := E) r R
    let s1 := 2 * R / (R ^ 2 - r ^ 2)
    let s2 := 2 / (R ^ 2 - r ^ 2)
    have hd1 : ‖d1‖ ≤ s1 := norm_ballCutoffArgumentFDeriv_le hr hrR hx
    have hd2 : ‖d2‖ ≤ s2 := norm_ballCutoffArgumentFDeriv2_le hr hrR
    have hs1 : 0 ≤ s1 := by
      have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
      exact div_nonneg (mul_nonneg (by norm_num) (hr.trans hrR.le)) hden.le
    refine ContinuousLinearMap.opNorm_le_bound _
      (ballCutoffFDeriv2Bound_nonneg hr hrR) ?_
    intro v
    let a := ballCutoffArgument center r R x
    have hd1v : |d1 v| ≤ s1 * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (d1.le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hd1 (norm_nonneg v))
    have hd2v : ‖d2 v‖ ≤ s2 * ‖v‖ :=
      (d2.le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hd2 (norm_nonneg v))
    have hterm1 : ‖deriv CutoffProfile.value a • d2 v‖ ≤
        (CutoffProfile.derivBound * s2) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |deriv CutoffProfile.value a| * ‖d2 v‖ ≤
            CutoffProfile.derivBound * (s2 * ‖v‖) :=
          mul_le_mul (CutoffProfile.abs_deriv_le_derivBound a) hd2v
            (norm_nonneg _) CutoffProfile.derivBound_nonneg
        _ = (CutoffProfile.derivBound * s2) * ‖v‖ := by ring
    have hcoefficient :
        |deriv (deriv CutoffProfile.value) a| * |d1 v| ≤
          CutoffProfile.derivBound * (s1 * ‖v‖) :=
      mul_le_mul (CutoffProfile.abs_deriv2_le_derivBound a) hd1v
        (abs_nonneg _) CutoffProfile.derivBound_nonneg
    have hterm2 : ‖(deriv (deriv CutoffProfile.value) a * d1 v) • d1‖ ≤
        (CutoffProfile.derivBound * s1 ^ 2) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      calc
        (|deriv (deriv CutoffProfile.value) a| * |d1 v|) * ‖d1‖ ≤
            (CutoffProfile.derivBound * (s1 * ‖v‖)) * s1 :=
          mul_le_mul hcoefficient hd1 (norm_nonneg _)
            (mul_nonneg CutoffProfile.derivBound_nonneg
              (mul_nonneg hs1 (norm_nonneg v)))
        _ = (CutoffProfile.derivBound * s1 ^ 2) * ‖v‖ := by ring
    change ‖deriv CutoffProfile.value a • d2 v +
      (deriv (deriv CutoffProfile.value) a * d1 v) • d1‖ ≤
        ballCutoffFDeriv2Bound r R * ‖v‖
    calc
      ‖deriv CutoffProfile.value a • d2 v +
          (deriv (deriv CutoffProfile.value) a * d1 v) • d1‖ ≤
          ‖deriv CutoffProfile.value a • d2 v‖ +
            ‖(deriv (deriv CutoffProfile.value) a * d1 v) • d1‖ :=
        norm_add_le _ _
      _ ≤ (CutoffProfile.derivBound * s2) * ‖v‖ +
          (CutoffProfile.derivBound * s1 ^ 2) * ‖v‖ :=
        add_le_add hterm1 hterm2
      _ = ballCutoffFDeriv2Bound r R * ‖v‖ := by
        simp only [ballCutoffFDeriv2Bound, s1, s2]
        ring
  · have harg : 2 ≤ ballCutoffArgument center r R x := by
      have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
      have hR : 0 ≤ R := hr.trans hrR.le
      have hdist : R ≤ ‖x - center‖ := by
        simpa [dist_eq_norm] using (not_le.mp hx).le
      have hsq : R ^ 2 ≤ ‖x - center‖ ^ 2 :=
        (sq_le_sq₀ hR (norm_nonneg _)).2 hdist
      have hquot : 1 ≤
          (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith
      simp only [ballCutoffArgument]
      linarith
    have hz : ballCutoffFDeriv2 center r R x = 0 := by
      ext v w
      simp [ballCutoffFDeriv2, CutoffProfile.deriv_zero_of_ge harg,
        CutoffProfile.deriv2_zero_of_ge harg, zero_smul,
        ContinuousLinearMap.zero_smulRight]
    rw [hz]
    have hzero : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0 :=
      ContinuousLinearMap.opNorm_zero
    rw [hzero]
    exact ballCutoffFDeriv2Bound_nonneg hr hrR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_ballCutoffFDeriv2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_ballCutoffFDeriv2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_ballCutoffFDeriv2_le ``Submission.DifferentialGeometry.Analysis.norm_ballCutoffFDeriv2_le

theorem ballCutoff_contDiff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    ContDiff ℝ ∞ (ballCutoff center r R) := by
  have hnorm : ContDiff ℝ ∞ (fun x : E ↦ ‖x - center‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have harg : ContDiff ℝ ∞ (ballCutoffArgument center r R) := by
    simpa [ballCutoffArgument] using!
      (contDiff_const.add ((hnorm.sub contDiff_const).div_const (R ^ 2 - r ^ 2)))
  simpa [ballCutoffArgument, ballCutoff] using!
    CutoffProfile.contDiff.comp harg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_contDiff ``Submission.DifferentialGeometry.Analysis.ballCutoff_contDiff

theorem fderiv_ballCutoff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    fderiv ℝ (ballCutoff center r R) = ballCutoffFDeriv center r R := by
  funext x
  exact (hasFDerivAt_ballCutoff center r R x).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_ballCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_ballCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_ballCutoff ``Submission.DifferentialGeometry.Analysis.fderiv_ballCutoff

theorem fderiv_ballCutoffFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    fderiv ℝ (ballCutoffFDeriv center r R) =
      ballCutoffFDeriv2 center r R := by
  funext x
  exact (hasFDerivAt_ballCutoffFDeriv center r R x).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_ballCutoffFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_ballCutoffFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_ballCutoffFDeriv ``Submission.DifferentialGeometry.Analysis.fderiv_ballCutoffFDeriv

theorem ballCutoffFDeriv_contDiff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    ContDiff ℝ ∞ (ballCutoffFDeriv center r R) := by
  rw [← fderiv_ballCutoff]
  exact (ballCutoff_contDiff center r R).fderiv_right (m := ∞) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv_contDiff ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv_contDiff

theorem ballCutoffFDeriv2_contDiff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    ContDiff ℝ ∞ (ballCutoffFDeriv2 center r R) := by
  rw [← fderiv_ballCutoffFDeriv]
  exact (ballCutoffFDeriv_contDiff center r R).fderiv_right
    (m := ∞) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2_contDiff ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2_contDiff

theorem ballCutoff_mem_Icc (center : E) (r R : ℝ) (x : E) :
    ballCutoff center r R x ∈ Set.Icc (0 : ℝ) 1 :=
  CutoffProfile.mem_Icc _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_mem_Icc ``Submission.DifferentialGeometry.Analysis.ballCutoff_mem_Icc

theorem ballCutoff_eq_one_of_mem_closedBall
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : E} (hx : x ∈ Metric.closedBall center r) :
    ballCutoff center r R x = 1 := by
  apply CutoffProfile.one_of_le_one
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hdist : ‖x - center‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hsq : ‖x - center‖ ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hr).2 hdist
  have hquot : (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) hden.le
  simp only [ballCutoffArgument]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_eq_one_of_mem_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_eq_one_of_mem_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_eq_one_of_mem_closedBall ``Submission.DifferentialGeometry.Analysis.ballCutoff_eq_one_of_mem_closedBall

theorem ballCutoff_eq_zero_of_le_dist
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : E} (hx : R ≤ _root_.Dist.dist x center) :
    ballCutoff center r R x = 0 := by
  apply CutoffProfile.zero_of_two_le
  have hR : 0 ≤ R := hr.trans hrR.le
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hdist : R ≤ ‖x - center‖ := by
    simpa [dist_eq_norm] using hx
  have hsq : R ^ 2 ≤ ‖x - center‖ ^ 2 :=
    (sq_le_sq₀ hR (norm_nonneg _)).2 hdist
  have hquot : 1 ≤ (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) := by
    rw [le_div_iff₀ hden]
    linarith
  simp only [ballCutoffArgument]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_le_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_le_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_le_dist ``Submission.DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_le_dist

theorem ballCutoff_eq_zero_of_not_mem_ball
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : E} (hx : x ∉ Metric.ball center R) :
    ballCutoff center r R x = 0 :=
  ballCutoff_eq_zero_of_le_dist hr hrR (by simpa [Metric.mem_ball, dist_comm] using hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_not_mem_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_not_mem_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_not_mem_ball ``Submission.DifferentialGeometry.Analysis.ballCutoff_eq_zero_of_not_mem_ball

theorem ballCutoff_support_subset_ball
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    Function.support (ballCutoff center r R) ⊆ Metric.ball center R := by
  intro x hx
  by_contra hxball
  exact hx (ballCutoff_eq_zero_of_not_mem_ball hr hrR hxball)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_support_subset_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_support_subset_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_support_subset_ball ``Submission.DifferentialGeometry.Analysis.ballCutoff_support_subset_ball

theorem ballCutoff_tsupport_subset_closedBall
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    tsupport (ballCutoff center r R) ⊆ Metric.closedBall center R := by
  exact (closure_mono (ballCutoff_support_subset_ball hr hrR)).trans
    Metric.closure_ball_subset_closedBall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_tsupport_subset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_tsupport_subset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_tsupport_subset_closedBall ``Submission.DifferentialGeometry.Analysis.ballCutoff_tsupport_subset_closedBall

theorem ballCutoff_hasCompactSupport
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (ballCutoff center r R) := by
  exact (_root_.ProperSpace.isCompact_closedBall center R).of_isClosed_subset
    isClosed_closure (ballCutoff_tsupport_subset_closedBall hr hrR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoff_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoff_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoff_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.ballCutoff_hasCompactSupport

theorem ballCutoffFDeriv_hasCompactSupport
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (ballCutoffFDeriv center r R) := by
  rw [← fderiv_ballCutoff]
  exact (ballCutoff_hasCompactSupport hr hrR).fderiv ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv_hasCompactSupport

theorem ballCutoffFDeriv2_hasCompactSupport
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (ballCutoffFDeriv2 center r R) := by
  rw [← fderiv_ballCutoffFDeriv]
  exact (ballCutoffFDeriv_hasCompactSupport hr hrR).fderiv ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ballCutoffFDeriv2_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ballCutoffFDeriv2_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ballCutoffFDeriv2_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.ballCutoffFDeriv2_hasCompactSupport

end DifferentialGeometry.Analysis

end
