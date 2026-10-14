import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

theorem norm_sq_div_add_inner_ge_neg_quarter_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {alpha : ℝ} (halpha : 0 < alpha) (p v : V) :
    -(alpha / 4) * ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 / alpha + _root_.Inner.inner ℝ p v := by
  have hinner : -(‖p‖ * ‖v‖) ≤ _root_.Inner.inner ℝ p v :=
    neg_le_of_abs_le (abs_real_inner_le_norm p v)
  have haux : -(alpha / 4) * ‖v‖ ^ 2 - _root_.Inner.inner ℝ p v ≤
      ‖p‖ ^ 2 / alpha := by
    apply (le_div_iff₀ halpha).2
    nlinarith [sq_nonneg (‖p‖ - alpha * ‖v‖ / 2)]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.norm_sq_div_add_inner_ge_neg_quarter_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.norm_sq_div_add_inner_ge_neg_quarter_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.norm_sq_div_add_inner_ge_neg_quarter_norm_sq ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.norm_sq_div_add_inner_ge_neg_quarter_norm_sq

theorem endpoint_difference_le_intervalIntegral_of_derivative_lower_bound
    {phi derivative bound : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hderivative : ContinuousOn derivative (_root_.Set.Icc a b))
    (hbound : ContinuousOn bound (_root_.Set.Icc a b))
    (hphi : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt phi (derivative t) t)
    (hlower : ∀ t ∈ _root_.Set.Icc a b, -bound t ≤ derivative t) :
    phi a - phi b ≤ ∫ t in a..b, bound t := by
  have hderivative_uIcc : ContinuousOn derivative (_root_.Set.uIcc a b) := by
    simpa [_root_.Set.uIcc_of_le hab] using hderivative
  have hbound_uIcc : ContinuousOn bound (_root_.Set.uIcc a b) := by
    simpa [_root_.Set.uIcc_of_le hab] using hbound
  have hderivative_int : IntervalIntegrable derivative _root_.MeasureTheory.MeasureSpace.volume a b :=
    hderivative_uIcc.intervalIntegrable
  have hbound_int : IntervalIntegrable bound _root_.MeasureTheory.MeasureSpace.volume a b :=
    hbound_uIcc.intervalIntegrable
  have hftc : (∫ t in a..b, derivative t) = phi b - phi a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hphi t (by simpa [_root_.Set.uIcc_of_le hab] using ht))
      hderivative_int
  have hmono : (∫ t in a..b, -bound t) ≤ ∫ t in a..b, derivative t :=
    intervalIntegral.integral_mono_on hab hbound_int.neg
      hderivative_int hlower
  rw [intervalIntegral.integral_neg, hftc] at hmono
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.endpoint_difference_le_intervalIntegral_of_derivative_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.endpoint_difference_le_intervalIntegral_of_derivative_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.endpoint_difference_le_intervalIntegral_of_derivative_lower_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.endpoint_difference_le_intervalIntegral_of_derivative_lower_bound

theorem harnack_endpoint_of_log_derivative_lower_bound
    {u logDerivative bound : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : ∀ t ∈ _root_.Set.Icc a b, 0 < u t)
    (hlogDerivative : ContinuousOn logDerivative (_root_.Set.Icc a b))
    (hbound : ContinuousOn bound (_root_.Set.Icc a b))
    (hlog : ∀ t ∈ _root_.Set.Icc a b,
      HasDerivAt (fun s => Real.log (u s)) (logDerivative t) t)
    (hlower : ∀ t ∈ _root_.Set.Icc a b, -bound t ≤ logDerivative t) :
    u a ≤ Real.exp (∫ t in a..b, bound t) * u b := by
  have hlog_bound : Real.log (u a) - Real.log (u b) ≤
      ∫ t in a..b, bound t :=
    endpoint_difference_le_intervalIntegral_of_derivative_lower_bound
      hab hlogDerivative hbound hlog hlower
  have hua : 0 < u a := hu a ⟨le_rfl, hab⟩
  have hub : 0 < u b := hu b ⟨hab, le_rfl⟩
  have hle : Real.log (u a) ≤
      (∫ t in a..b, bound t) + Real.log (u b) := by
    linarith
  have hexp := (Real.log_le_iff_le_exp hua).mp hle
  rw [Real.exp_add, Real.exp_log hub] at hexp
  exact hexp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_log_derivative_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_log_derivative_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_log_derivative_lower_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_log_derivative_lower_bound

theorem harnack_endpoint_of_derivative_lower_bound
    {u derivative bound : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : ∀ t ∈ _root_.Set.Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (_root_.Set.Icc a b))
    (hbound : ContinuousOn bound (_root_.Set.Icc a b))
    (hu_deriv : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (derivative t) t)
    (hlower : ∀ t ∈ _root_.Set.Icc a b, -bound t ≤ derivative t / u t) :
    u a ≤ Real.exp (∫ t in a..b, bound t) * u b := by
  have hu_cont : ContinuousOn u (_root_.Set.Icc a b) := by
    intro t ht
    exact (hu_deriv t ht).continuousAt.continuousWithinAt
  have hratio : ContinuousOn (fun t => derivative t / u t) (_root_.Set.Icc a b) :=
    hderivative.div hu_cont (fun t ht => (hu t ht).ne')
  apply harnack_endpoint_of_log_derivative_lower_bound
    hab hu hratio hbound
  · intro t ht
    exact (hu_deriv t ht).log (hu t ht).ne'
  · exact hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound

theorem harnack_endpoint_of_derivative_lower_bound_with_time_pole
    {u derivative error : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ _root_.Set.Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (_root_.Set.Icc a b))
    (herror : ContinuousOn error (_root_.Set.Icc a b))
    (hu_deriv : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (derivative t) t)
    (hlower : ∀ t ∈ _root_.Set.Icc a b,
      -(c / t + error t) ≤ derivative t / u t) :
    u a ≤ (b / a) ^ c * Real.exp (∫ t in a..b, error t) * u b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hdiv : ContinuousOn (fun t : ℝ => c / t) (_root_.Set.Icc a b) :=
    continuousOn_const.div continuousOn_id
      (fun t ht => (lt_of_lt_of_le ha ht.1).ne')
  have htotal : ContinuousOn (fun t => c / t + error t) (_root_.Set.Icc a b) :=
    hdiv.add herror
  have hmain := harnack_endpoint_of_derivative_lower_bound
    hab hu hderivative htotal hu_deriv hlower
  have hdiv_uIcc : ContinuousOn (fun t : ℝ => c / t) (_root_.Set.uIcc a b) := by
    simpa [_root_.Set.uIcc_of_le hab] using hdiv
  have herror_uIcc : ContinuousOn error (_root_.Set.uIcc a b) := by
    simpa [_root_.Set.uIcc_of_le hab] using herror
  have hdiv_int : IntervalIntegrable (fun t : ℝ => c / t) _root_.MeasureTheory.MeasureSpace.volume a b :=
    hdiv_uIcc.intervalIntegrable
  have herror_int : IntervalIntegrable error _root_.MeasureTheory.MeasureSpace.volume a b :=
    herror_uIcc.intervalIntegrable
  have hintegral : (∫ t in a..b, c / t + error t) =
      c * Real.log (b / a) + ∫ t in a..b, error t := by
    rw [intervalIntegral.integral_add hdiv_int herror_int]
    have hrewrite : (fun t : ℝ => c / t) = fun t => c * (1 / t) := by
      funext t
      ring
    rw [hrewrite, intervalIntegral.integral_const_mul,
      integral_one_div_of_pos ha hb]
  rw [hintegral, Real.exp_add] at hmain
  have hratio : 0 < b / a := div_pos hb ha
  rw [show Real.exp (c * Real.log (b / a)) = (b / a) ^ c by
    rw [Real.rpow_def_of_pos hratio]
    congr 1
    ring] at hmain
  exact hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole

theorem harnack_endpoint_of_derivative_lower_bound_with_time_pole_and_constant
    {u derivative : ℝ → ℝ} {a b c K : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ _root_.Set.Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (_root_.Set.Icc a b))
    (hu_deriv : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (derivative t) t)
    (hlower : ∀ t ∈ _root_.Set.Icc a b,
      -(c / t + K) ≤ derivative t / u t) :
    u a ≤ (b / a) ^ c * Real.exp (K * (b - a)) * u b := by
  have hmain := harnack_endpoint_of_derivative_lower_bound_with_time_pole
    (u := u) (derivative := derivative) (error := fun _ => K)
    ha hab hu hderivative continuousOn_const hu_deriv hlower
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole_and_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole_and_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole_and_constant ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_derivative_lower_bound_with_time_pole_and_constant

theorem harnack_endpoint_of_li_yau_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u derivative timePart : ℝ → ℝ} {gradient velocity : ℝ → V}
    {a b c alpha : ℝ}
    (halpha : 0 < alpha) (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ _root_.Set.Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (_root_.Set.Icc a b))
    (hvelocity : ContinuousOn velocity (_root_.Set.Icc a b))
    (hu_deriv : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (derivative t) t)
    (hpath : ∀ t ∈ _root_.Set.Icc a b, derivative t / u t =
      timePart t + _root_.Inner.inner ℝ (gradient t) (velocity t))
    (hliYau : ∀ t ∈ _root_.Set.Icc a b,
      -(c / t) + ‖gradient t‖ ^ 2 / alpha ≤ timePart t) :
    u a ≤ (b / a) ^ c *
      Real.exp (∫ t in a..b, alpha / 4 * ‖velocity t‖ ^ 2) * u b := by
  apply harnack_endpoint_of_derivative_lower_bound_with_time_pole
    (u := u) (derivative := derivative)
    (error := fun t => alpha / 4 * ‖velocity t‖ ^ 2)
    ha hab hu hderivative
  · exact continuousOn_const.mul (hvelocity.norm.pow 2)
  · exact hu_deriv
  · intro t ht
    rw [hpath t ht]
    have hyoung := norm_sq_div_add_inner_ge_neg_quarter_norm_sq
      halpha (gradient t) (velocity t)
    nlinarith [hliYau t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound

theorem harnack_endpoint_of_li_yau_bound_abstract
    {u derivative timePart gradSq innerGV speedSq : ℝ → ℝ} {a b c alpha : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ _root_.Set.Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (_root_.Set.Icc a b))
    (hspeed : ContinuousOn speedSq (_root_.Set.Icc a b))
    (hu_deriv : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (derivative t) t)
    (hpath : ∀ t ∈ _root_.Set.Icc a b, derivative t / u t = timePart t + innerGV t)
    (hliYau : ∀ t ∈ _root_.Set.Icc a b, -(c / t) + gradSq t / alpha ≤ timePart t)
    (hquad : ∀ t ∈ _root_.Set.Icc a b, -(alpha / 4) * speedSq t ≤ gradSq t / alpha + innerGV t) :
    u a ≤ (b / a) ^ c * Real.exp (∫ t in a..b, alpha / 4 * speedSq t) * u b := by
  apply harnack_endpoint_of_derivative_lower_bound_with_time_pole
    (u := u) (derivative := derivative)
    (error := fun t => alpha / 4 * speedSq t)
    ha hab hu hderivative
  · exact continuousOn_const.mul hspeed
  · exact hu_deriv
  · intro t ht
    rw [hpath t ht]
    have hly := hliYau t ht
    have hq := hquad t ht
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound_abstract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound_abstract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound_abstract ``Submission.DifferentialGeometry.Analysis.Parabolic.Harnack.harnack_endpoint_of_li_yau_bound_abstract

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
