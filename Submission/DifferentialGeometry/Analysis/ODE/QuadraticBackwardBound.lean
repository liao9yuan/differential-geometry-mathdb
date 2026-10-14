import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.FieldSimp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Filter
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.ODE

theorem le_of_quadratic_deriv_bound
    {r r' : ℝ → ℝ} {a b q A B t : ℝ} {C : ℝ≥0}
    (hA : 0 < A) (hB : 0 < B) (hqA : q ≤ A)
    (hc : ContinuousOn r (_root_.Set.Icc a b))
    (hd : ∀ s ∈ _root_.Set.Ioo a b, q < r s → HasDerivAt r (r' s) s)
    (hb : ∀ s ∈ _root_.Set.Ioo a b, q < r s → |r' s| ≤ C * r s ^ 2)
    (hend : r b ≤ A) (ht : t ∈ _root_.Set.Icc a b)
    (htime : C * (b - t) ≤ A⁻¹ - B⁻¹) : r t ≤ B := by
  have hlip := DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    hA hc (fun s hs hAs => hd s hs (hqA.trans_lt hAs))
    (fun s hs hAs => hb s hs (hqA.trans_lt hAs))
  have hrec := hlip.dist_le_mul b ⟨ht.1.trans ht.2, le_rfl⟩ t ht
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2),
    max_eq_left hend] at hrec
  have hlow : B⁻¹ ≤ (_root_.Max.max A (r t))⁻¹ := by linarith [(le_abs_self (A⁻¹ - (_root_.Max.max A (r t))⁻¹))]
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ hB (hA.trans_le (le_max_left _ _))).mp hlow)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.le_of_quadratic_deriv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.le_of_quadratic_deriv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.le_of_quadratic_deriv_bound ``Submission.DifferentialGeometry.Analysis.ODE.le_of_quadratic_deriv_bound

theorem eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {r r' : ι → ℝ → X → ℝ} {rInf : X → ℝ}
    {q : ι → ℝ} {σ b ε : ℝ} {C : ℝ≥0}
    (htime : 6 * C * ε * _root_.Max.max σ 1 ≤ 1)
    (hconv : TendstoUniformlyOn (fun i x => r i b x) rInf l K)
    (hlim : ∀ x ∈ K, rInf x ≤ σ)
    (hq : ∀ᶠ i in l, q i ≤ _root_.Max.max σ 1)
    (hc : ∀ᶠ i in l, ∀ x ∈ K, ContinuousOn (fun t => r i t x) (_root_.Set.Icc (b - ε) b))
    (hd : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (b - ε) b,
      q i < r i t x → HasDerivAt (fun s => r i s x) (r' i t x) t)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (b - ε) b,
      q i < r i t x → |r' i t x| ≤ C * r i t x ^ 2) :
    ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ _root_.Set.Icc (b - ε) b, r i t x ≤ 2 * _root_.Max.max σ 1 := by
  let Q := _root_.Max.max σ 1
  have hQ : 0 < Q := zero_lt_one.trans_le (le_max_right _ _)
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hconv) (Q / 2) (by positivity)
  filter_upwards [hq, hc, hd, hb, hclose] with i hiq hic hid hib hiclose
  intro x hx t ht
  have hend : r i b x ≤ (3 / 2 : ℝ) * Q := by
    have hdist := hiclose x hx
    rw [Real.dist_eq] at hdist
    have hsQ : σ ≤ Q := le_max_left _ _
    have hdiff := (abs_lt.mp hdist).1
    have hlimx := hlim x hx
    linarith
  apply le_of_quadratic_deriv_bound (q := q i) (r' := fun s => r' i s x)
    (by positivity : 0 < (3 / 2 : ℝ) * Q) (by positivity : 0 < 2 * Q)
    (by dsimp [Q] at *; linarith) (hic x hx) (hid x hx) (hib x hx) hend ht
  have hsmall : C * (b - t) ≤ (6 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    have htε : b - t ≤ ε := by linarith [ht.1]
    have hmul := mul_le_mul_of_nonneg_left htε C.coe_nonneg
    change 6 * C * ε * Q ≤ 1 at htime
    nlinarith
  have heq : ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ = (6 * Q)⁻¹ := by
    field_simp
    ring
  rw [heq]
  exact hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound ``Submission.DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound

theorem eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {r r' : ι → ℝ → X → ℝ} {q : ι → ℝ} {σ b : ℝ} {C : ℝ≥0}
    (hC : 0 < C)
    (hconv : TendstoUniformlyOn (fun i x => r i b x) (fun _ => σ) l K)
    (hq : ∀ᶠ i in l, q i ≤ _root_.Max.max σ 1)
    (hc : ∀ᶠ i in l, ∀ x ∈ K,
      ContinuousOn (fun t => r i t x) (_root_.Set.Icc (b - (6 * C * _root_.Max.max σ 1)⁻¹) b))
    (hd : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (b - (6 * C * _root_.Max.max σ 1)⁻¹) b,
      q i < r i t x → HasDerivAt (fun s => r i s x) (r' i t x) t)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (b - (6 * C * _root_.Max.max σ 1)⁻¹) b,
      q i < r i t x → |r' i t x| ≤ C * r i t x ^ 2) :
    0 < (6 * C * _root_.Max.max σ 1)⁻¹ ∧
      ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ _root_.Set.Icc (b - (6 * C * _root_.Max.max σ 1)⁻¹) b,
        r i t x ≤ 2 * _root_.Max.max σ 1 := by
  have hQ : 0 < _root_.Max.max σ 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hC' : 0 < (C : ℝ) := hC
  have hpos : 0 < 6 * (C : ℝ) * _root_.Max.max σ 1 := by positivity
  refine ⟨inv_pos.mpr hpos, ?_⟩
  apply eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound
    (σ := σ) (C := C) ?_ hconv (fun _ _ => le_rfl) hq hc hd hb
  have heq : 6 * C * (6 * C * _root_.Max.max σ 1)⁻¹ * _root_.Max.max σ 1 = 1 := by
    calc
      6 * C * (6 * C * _root_.Max.max σ 1)⁻¹ * _root_.Max.max σ 1 =
          (6 * C * _root_.Max.max σ 1) * (6 * C * _root_.Max.max σ 1)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  exact heq.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn ``Submission.DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn

end DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Analysis

theorem derivWithin_const_mul_comp_affine_Iic
    {f : ℝ → ℝ} {T Q s : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.Iic (T + s / Q)) (T + s / Q)) :
    derivWithin (fun u => Q⁻¹ * f (T + u / Q)) (_root_.Set.Iic s) s =
      Q⁻¹ ^ 2 * derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q) := by
  have htime : HasDerivAt (fun u : ℝ => T + u / Q) Q⁻¹ s := by
    have hh : HasDerivAt (fun u : ℝ => u / Q) (1 / Q) s :=
      (hasDerivAt_id s).div_const Q
    rw [one_div] at hh
    exact hh.const_add T
  have hmaps : _root_.Set.MapsTo (fun u : ℝ => T + u / Q) (_root_.Set.Iic s) (_root_.Set.Iic (T + s / Q)) := by
    intro u hu
    exact add_le_add_right (div_le_div_of_nonneg_right hu hQ.le) T
  have hd := (hf.hasDerivWithinAt.comp s htime.hasDerivWithinAt hmaps).const_mul Q⁻¹
  calc
    _ = Q⁻¹ * (derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q) * Q⁻¹) :=
      hd.derivWithin (uniqueDiffWithinAt_Iic s)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.derivWithin_const_mul_comp_affine_Iic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.derivWithin_const_mul_comp_affine_Iic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.derivWithin_const_mul_comp_affine_Iic ``Submission.DifferentialGeometry.Analysis.derivWithin_const_mul_comp_affine_Iic

theorem abs_derivWithin_comp_affine_le_sq
    {f : ℝ → ℝ} {T Q s q C : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.Iic (T + s / Q)) (T + s / Q))
    (hb : q < f (T + s / Q) →
      |derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q)| ≤ C * f (T + s / Q) ^ 2)
    (hhigh : q / Q < Q⁻¹ * f (T + s / Q)) :
    |derivWithin (fun u => Q⁻¹ * f (T + u / Q)) (_root_.Set.Iic s) s| ≤
      C * (Q⁻¹ * f (T + s / Q)) ^ 2 := by
  have hh : q < f (T + s / Q) := by
    rw [inv_mul_eq_div] at hhigh
    exact (div_lt_div_iff_of_pos_right hQ).mp hhigh
  rw [derivWithin_const_mul_comp_affine_Iic hQ hf, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    Q⁻¹ ^ 2 * |derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q)| ≤
        Q⁻¹ ^ 2 * (C * f (T + s / Q) ^ 2) :=
      mul_le_mul_of_nonneg_left (hb hh) (sq_nonneg _)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq ``Submission.DifferentialGeometry.Analysis.abs_derivWithin_comp_affine_le_sq

theorem abs_derivWithin_le_sq_iff_comp_affine
    {f : ℝ → ℝ} {T Q s C : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.Iic (T + s / Q)) (T + s / Q)) :
    (|derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q)| ≤ C * f (T + s / Q) ^ 2) ↔
      |derivWithin (fun u => Q⁻¹ * f (T + u / Q)) (_root_.Set.Iic s) s| ≤
        C * (Q⁻¹ * f (T + s / Q)) ^ 2 := by
  rw [derivWithin_const_mul_comp_affine_Iic hQ hf, abs_mul]
  simp only [abs_of_nonneg (sq_nonneg (Q⁻¹))]
  have heq : C * (Q⁻¹ * f (T + s / Q)) ^ 2 = Q⁻¹ ^ 2 * (C * f (T + s / Q) ^ 2) := by ring
  rw [heq]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hQ))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_comp_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_comp_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_comp_affine ``Submission.DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_comp_affine


theorem abs_derivWithin_le_sq_iff_of_eventuallyEq_comp_affine
    {f fhat : ℝ → ℝ} {T Q s C : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.Iic (T + s / Q)) (T + s / Q))
    (heq : fhat =ᶠ[𝓝[_root_.Set.Iic s] s] fun u => Q⁻¹ * f (T + u / Q)) :
    (|derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q)| ≤ C * f (T + s / Q) ^ 2) ↔
      |derivWithin fhat (_root_.Set.Iic s) s| ≤ C * fhat s ^ 2 := by
  rw [heq.derivWithin_eq_of_mem (mem_Iic.mpr le_rfl),
    heq.eq_of_nhdsWithin (mem_Iic.mpr le_rfl)]
  exact abs_derivWithin_le_sq_iff_comp_affine hQ hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eventuallyEq_comp_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eventuallyEq_comp_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eventuallyEq_comp_affine ``Submission.DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eventuallyEq_comp_affine

theorem abs_derivWithin_le_sq_iff_of_eqOn_comp_affine_Icc
    {f fhat : ℝ → ℝ} {T Q a b s C : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.Iic (T + s / Q)) (T + s / Q))
    (heq : _root_.Set.EqOn fhat (fun u => Q⁻¹ * f (T + u / Q)) (_root_.Set.Icc a b))
    (hs : s ∈ _root_.Set.Ioc a b) :
    (|derivWithin f (_root_.Set.Iic (T + s / Q)) (T + s / Q)| ≤ C * f (T + s / Q) ^ 2) ↔
      |derivWithin fhat (_root_.Set.Iic s) s| ≤ C * fhat s ^ 2 := by
  apply abs_derivWithin_le_sq_iff_of_eventuallyEq_comp_affine hQ hf
  filter_upwards [Icc_mem_nhdsLE_of_mem hs] with u hu
  exact heq hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eqOn_comp_affine_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eqOn_comp_affine_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eqOn_comp_affine_Icc ``Submission.DifferentialGeometry.Analysis.abs_derivWithin_le_sq_iff_of_eqOn_comp_affine_Icc



theorem differentiableWithinAt_of_eqOn_comp_affine_Icc
    {f fhat : ℝ → ℝ} {T Q a b s : ℝ} (hQ : 0 < Q)
    (hfhat : DifferentiableWithinAt ℝ fhat (_root_.Set.Icc a b) s)
    (heq : _root_.Set.EqOn fhat (fun u => Q⁻¹ * f (T + u / Q)) (_root_.Set.Icc a b))
    (hs : s ∈ _root_.Set.Ioc a b) :
    DifferentiableWithinAt ℝ f (_root_.Set.Iic (T + s / Q)) (T + s / Q) := by
  have hback : Q * (T + s / Q - T) = s := by field_simp; ring
  have hdhat : DifferentiableWithinAt ℝ fhat (_root_.Set.Iic s) (Q * (T + s / Q - T)) := by
    rw [hback]
    exact hfhat.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem hs)
  have hdback : DifferentiableWithinAt ℝ (fun t => Q * (t - T))
      (_root_.Set.Iic (T + s / Q)) (T + s / Q) := by fun_prop
  have hmaps : _root_.Set.MapsTo (fun t => Q * (t - T)) (_root_.Set.Iic (T + s / Q)) (_root_.Set.Iic s) := by
    intro t ht
    change Q * (t - T) ≤ s
    rw [← hback]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht T) hQ.le
  have hd := (hdhat.comp (T + s / Q) hdback hmaps).const_mul Q
  apply hd.congr_of_eventuallyEq_of_mem ?_ (mem_Iic.mpr le_rfl)
  have hphys : T + s / Q ∈ _root_.Set.Ioc (T + a / Q) (T + b / Q) := by
    constructor
    · have h := div_lt_div_of_pos_right hs.1 hQ
      linarith
    · have h := div_le_div_of_nonneg_right hs.2 hQ.le
      linarith
  filter_upwards [Icc_mem_nhdsLE_of_mem hphys] with t ht
  have hnorm : Q * (t - T) ∈ _root_.Set.Icc a b := by
    constructor
    · have h := (div_le_iff₀ hQ).mp (show a / Q ≤ t - T by linarith [ht.1])
      nlinarith
    · have h := (le_div_iff₀ hQ).mp (show t - T ≤ b / Q by linarith [ht.2])
      nlinarith
  have htime : T + Q * (t - T) / Q = t := by field_simp; ring
  have hvalue := heq hnorm
  dsimp only at hvalue
  rw [htime] at hvalue
  change f t = Q * fhat (Q * (t - T))
  rw [hvalue, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.differentiableWithinAt_of_eqOn_comp_affine_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.differentiableWithinAt_of_eqOn_comp_affine_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.differentiableWithinAt_of_eqOn_comp_affine_Icc ``Submission.DifferentialGeometry.Analysis.differentiableWithinAt_of_eqOn_comp_affine_Icc


end DifferentialGeometry.Analysis
