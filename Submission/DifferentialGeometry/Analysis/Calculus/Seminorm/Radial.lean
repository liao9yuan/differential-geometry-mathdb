import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Calculus

section RadialLengthAnalyticEngine

open _root_.MeasureTheory _root_.intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma psd_cauchy_schwarz (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    (B x y) ^ 2 ≤ B x x * B y y := by
  by_cases hy : B y y = 0
  · have key : ∀ t : ℝ, 0 ≤ B x x - 2 * t * B x y := by
      intro t
      have h := hnn (x - t • y)
      have expand : B (x - t • y) (x - t • y) = B x x - 2 * t * B x y + t ^ 2 * B y y := by
        simp only [map_sub, map_smul, sub_apply,
          smul_apply, smul_eq_mul]
        rw [hsym y x]; ring
      rw [expand, hy] at h; linarith [h]
    rw [hy, _root_.MulZeroClass.mul_zero]
    by_contra hcon
    rw [not_le] at hcon
    have hxy : B x y ≠ 0 := by intro h0; rw [h0] at hcon; norm_num at hcon
    have h2 : 2 * ((B x x + 1) / (2 * B x y)) * B x y = B x x + 1 := by field_simp
    have := key ((B x x + 1) / (2 * B x y))
    rw [h2] at this; linarith
  · have hpos : 0 < B y y := lt_of_le_of_ne (hnn y) (Ne.symm hy)
    have h := hnn (x - (B x y / B y y) • y)
    have expand : B (x - (B x y / B y y) • y) (x - (B x y / B y y) • y)
        = B x x - (B x y) ^ 2 / B y y := by
      simp only [map_sub, map_smul, sub_apply,
        smul_apply, smul_eq_mul]
      rw [hsym y x]; field_simp; ring
    rw [expand] at h
    have hb : (B x y) ^ 2 / B y y ≤ B x x := by linarith
    have := (div_le_iff₀ hpos).mp hb
    linarith [this]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.psd_cauchy_schwarz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.psd_cauchy_schwarz target :: scope.openDecls } }

private lemma psd_seminorm_triangle (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    Real.sqrt (B (x + y) (x + y)) ≤ Real.sqrt (B x x) + Real.sqrt (B y y) := by
  have hxx := hnn x; have hyy := hnn y
  have hcs := psd_cauchy_schwarz B hsym hnn x y
  have hexp : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    simp only [map_add, add_apply]; rw [hsym y x]; ring
  have hbxy_le : B x y ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
    have h1 : B x y ≤ |B x y| := le_abs_self _
    have h2 : |B x y| ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hxx]
      exact Real.sqrt_le_sqrt hcs
    linarith
  have hrhs : (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2
      = B x x + 2 * (Real.sqrt (B x x) * Real.sqrt (B y y)) + B y y := by
    rw [add_sq, Real.sq_sqrt hxx, Real.sq_sqrt hyy]; ring
  have hle : B (x + y) (x + y) ≤ (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2 := by
    rw [hexp, hrhs]; linarith
  calc Real.sqrt (B (x + y) (x + y))
        ≤ Real.sqrt ((Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (B x x) + Real.sqrt (B y y) := by rw [Real.sqrt_sq (by positivity)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.psd_seminorm_triangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.psd_seminorm_triangle target :: scope.openDecls } }

private lemma psd_reverse_triangle (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    |Real.sqrt (B x x) - Real.sqrt (B y y)| ≤ Real.sqrt (B (x - y) (x - y)) := by
  have h1 : Real.sqrt (B x x) ≤ Real.sqrt (B (x - y) (x - y)) + Real.sqrt (B y y) := by
    have := psd_seminorm_triangle B hsym hnn (x - y) y
    rwa [sub_add_cancel] at this
  have h2 : Real.sqrt (B y y) ≤ Real.sqrt (B (y - x) (y - x)) + Real.sqrt (B x x) := by
    have := psd_seminorm_triangle B hsym hnn (y - x) x
    rwa [sub_add_cancel] at this
  have hsymq : B (y - x) (y - x) = B (x - y) (x - y) := by
    have hyx : y - x = -(x - y) := by abel
    rw [hyx]
    simp only [map_neg, neg_apply, neg_neg]
  rw [hsymq] at h2
  rw [abs_sub_le_iff]; constructor <;> linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.psd_reverse_triangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.psd_reverse_triangle target :: scope.openDecls } }

lemma psd_sqrt_lipschitz (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) :
    LipschitzWith (Real.toNNReal (Real.sqrt ‖B‖)) (fun x => Real.sqrt (B x x)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm]
  have hb0 : (0 : ℝ) ≤ ‖B‖ := by positivity
  calc |Real.sqrt (B x x) - Real.sqrt (B y y)|
        ≤ Real.sqrt (B (x - y) (x - y)) := psd_reverse_triangle B hsym hnn x y
    _ ≤ Real.sqrt ‖B‖ * ‖x - y‖ := by
        have hbz : B (x - y) (x - y) ≤ ‖B‖ * (‖x - y‖ * ‖x - y‖) := by
          calc B (x - y) (x - y) ≤ ‖B (x - y) (x - y)‖ := le_abs_self _
            _ ≤ ‖B‖ * ‖x - y‖ * ‖x - y‖ := B.le_opNorm₂ (x - y) (x - y)
            _ = ‖B‖ * (‖x - y‖ * ‖x - y‖) := by ring
        calc Real.sqrt (B (x - y) (x - y))
              ≤ Real.sqrt (‖B‖ * (‖x - y‖ * ‖x - y‖)) := Real.sqrt_le_sqrt hbz
          _ = Real.sqrt ‖B‖ * ‖x - y‖ := by
              rw [Real.sqrt_mul hb0, show ‖x - y‖ * ‖x - y‖ = ‖x - y‖ ^ 2 by ring,
                Real.sqrt_sq (norm_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.psd_sqrt_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.psd_sqrt_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.psd_sqrt_lipschitz ``Submission.DifferentialGeometry.Analysis.Calculus.psd_sqrt_lipschitz

lemma angular_hasDerivAt_zero (B : F →L[ℝ] F →L[ℝ] ℝ)
    {c : ℝ → F} {c' : F} {ρ : ℝ → ℝ} {t : ℝ}
    (hc : HasDerivAt c c' t) (hρt : 0 < ρ t)
    (hρ : HasDerivAt ρ (B (c t) c' / ρ t) t)
    (hρsq : ρ t ^ 2 = B (c t) (c t))
    (hrad : c' = (B (c t) c' / B (c t) (c t)) • c t) :
    HasDerivAt (fun s => (ρ s)⁻¹ • c s) 0 t := by
  have hrne : ρ t ≠ 0 := ne_of_gt hρt
  have hBne : B (c t) (c t) ≠ 0 := by rw [← hρsq]; positivity
  set k : ℝ := B (c t) c' with hk_def
  have hinv : HasDerivAt (fun s => (ρ s)⁻¹) (-(k / ρ t) / (ρ t)^2) t := by
    have h := hρ.inv hrne
    change HasDerivAt (fun s => (ρ s)⁻¹)
      (-((B (c t) c' / ρ t)) / (ρ t) ^ 2) t at h
    simpa only [hk_def] using h
  have hθ' : HasDerivAt (fun s => (ρ s)⁻¹ • c s)
      ((ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t)^2) • c t) t := by
    have h := hinv.smul hc
    change HasDerivAt (fun s => (ρ s)⁻¹ • c s)
      ((ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t) ^ 2) • c t) t at h
    exact h
  have hzero : (ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t)^2) • c t = 0 := by
    rw [hrad]
    rw [smul_smul, ← add_smul]
    rw [show (ρ t)⁻¹ * (k / B (c t) (c t)) + -(k / ρ t) / ρ t ^ 2 = 0 by
      rw [← hρsq]; field_simp; ring]
    rw [zero_smul]
  rwa [hzero] at hθ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.angular_hasDerivAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.angular_hasDerivAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.angular_hasDerivAt_zero ``Submission.DifferentialGeometry.Analysis.Calculus.angular_hasDerivAt_zero

lemma image_radialDist_le_intervalIntegral_of_slope_le
    {ρ φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρc : ContinuousOn ρ (Set.Icc a b)) (hρa : ρ a ≤ 0)
    (hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume)
    (hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x)
    (hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r) :
    ρ b ≤ ∫ t in a..b, φ t := by
  set B : ℝ → ℝ := fun x => ∫ t in a..x, φ t with hB
  have hφii : IntervalIntegrable φ _root_.MeasureTheory.MeasureSpace.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hφint
  have hBa : ρ a ≤ B a := by simp [hB, hρa]
  have hBcont : ContinuousOn B (Set.Icc a b) := by
    have h := _root_.intervalIntegral.continuousOn_primitive_interval' (f := φ) (μ := _root_.MeasureTheory.MeasureSpace.volume) (a := a)
      (b₁ := a) (b₂ := b) hφii Set.left_mem_uIcc
    rw [Set.uIcc_of_le hab] at h; exact h
  have hBderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt B (φ x) (Set.Ici x) x := by
    intro x hx
    have hcwa : ContinuousWithinAt φ (Set.Ioi x) x := hφcont x hx
    have hmem : Set.Icc a b ∈ nhdsWithin x (Set.Ioi x) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
    have hmeas : StronglyMeasurableAtFilter φ (nhdsWithin x (Set.Ioi x)) volume :=
      ⟨Set.Icc a b, hmem, hφint.aestronglyMeasurable⟩
    have hint_sub : IntervalIntegrable φ _root_.MeasureTheory.MeasureSpace.volume a x :=
      hφii.mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc le_rfl hx.2.le)
    exact intervalIntegral.integral_hasDerivWithinAt_right hint_sub hmeas hcwa
  exact image_le_of_liminf_slope_right_le_deriv_boundary hρc hBa hBcont hBderiv hslope
    (Set.right_mem_Icc.2 hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.image_radialDist_le_intervalIntegral_of_slope_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.image_radialDist_le_intervalIntegral_of_slope_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.image_radialDist_le_intervalIntegral_of_slope_le ``Submission.DifferentialGeometry.Analysis.Calculus.image_radialDist_le_intervalIntegral_of_slope_le

private lemma ftc_fencing_equality_case
    {ρ φ ρ' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρc : ContinuousOn ρ (Set.Icc a b))
    (hρderiv : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt ρ (ρ' x) (Set.Ioi x) x)
    (hρ'int : IntervalIntegrable ρ' MeasureTheory.volume a b)
    (hφint : MeasureTheory.IntegrableOn φ (Set.Ioo a b) MeasureTheory.volume)
    (hρ'φ : ∀ x ∈ Set.Ioo a b, ρ' x ≤ φ x)
    (htight : ρ b - ρ a = ∫ t in a..b, φ t) :
    ρ' =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] φ := by
  have hftc : (∫ t in a..b, ρ' t) = ρ b - ρ a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hρc hρderiv hρ'int
  have heqint : (∫ t in a..b, ρ' t) = ∫ t in a..b, φ t := by rw [hftc, htight]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at heqint
  have hconvρ : (∫ t in Set.Ioc a b, ρ' t) = ∫ t in Set.Ioo a b, ρ' t :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hconvφ : (∫ t in Set.Ioc a b, φ t) = ∫ t in Set.Ioo a b, φ t :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hconvρ, hconvφ] at heqint
  have hρ'Ioo : MeasureTheory.IntegrableOn ρ' (Set.Ioo a b) MeasureTheory.volume := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hρ'int; exact hρ'int
  have hae_le : ρ' ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] φ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hρ'φ
  exact (MeasureTheory.integral_eq_iff_of_ae_le hρ'Ioo hφint hae_le).mp heqint

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.ftc_fencing_equality_case
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.ftc_fencing_equality_case target :: scope.openDecls } }

end RadialLengthAnalyticEngine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open _root_.MeasureTheory in
open _root_.ContDiffOn in
theorem _root_.Submission.ContDiffOn.norm_sub_le_integral_of_inner_deriv_le
    {η : ℝ → V} {φ : ℝ → ℝ} {a b : ℝ} (hη : ContDiffOn ℝ 1 η (_root_.Set.Icc a b))
    (hab : a ≤ b) (hφ : IntervalIntegrable φ _root_.MeasureTheory.MeasureSpace.volume a b)
    (hφnn : ∀ t ∈ _root_.Set.Ioo a b, 0 ≤ φ t)
    (hrad : ∀ t ∈ _root_.Set.Ioo a b,
      Inner.inner ℝ (η t) (deriv η t) ≤ ‖η t‖ * φ t) :
    ‖η b‖ - ‖η a‖ ≤ ∫ t in a..b, φ t := by
  have hηac : AbsolutelyContinuousOnInterval η a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [_root_.Set.uIcc_of_le hab] using hη
  have hρac : AbsolutelyContinuousOnInterval (fun t => ‖η t‖) a b :=
    lipschitzWith_one_norm.lipschitzOnWith.comp_absolutelyContinuousOnInterval
      hηac (fun _ _ => _root_.Set.mem_univ _)
  have hderiv : ∀ t ∈ _root_.Set.Ioo a b, deriv (fun s => ‖η s‖) t ≤ φ t := by
    intro t ht
    by_cases hη0 : η t = 0
    · have hmin : IsLocalMin (fun s => ‖η s‖) t := by
        filter_upwards with s
        simpa only [hη0, norm_zero] using norm_nonneg (η s)
      rw [hmin.deriv_eq_zero]
      exact hφnn t ht
    · have hηdiff : DifferentiableAt ℝ η t :=
        ((hη.differentiableOn one_ne_zero) t (_root_.Set.Ioo_subset_Icc_self ht)).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)
      have hd := hηdiff.hasDerivAt.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hη0))
      have hnorm : HasDerivAt (fun s => ‖η s‖)
          (Inner.inner ℝ (η t) (deriv η t) / ‖η t‖) t := by
        convert hd using 1
        · funext s
          exact (Real.sqrt_sq (norm_nonneg (η s))).symm
        · rw [Real.sqrt_sq (norm_nonneg _)]
          rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [hnorm.deriv]
      exact (div_le_iff₀ (norm_pos_iff.mpr hη0)).mpr (by simpa only [mul_comm] using hrad t ht)
  rw [← hρac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_mono_ae_restrict hab hρac.intervalIntegrable_deriv hφ
  change ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), deriv (fun s => ‖η s‖) t ≤ φ t
  rw [_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [_root_.MeasureTheory.Ioo_ae_eq_Icc (μ := _root_.MeasureTheory.MeasureSpace.volume)] with t ht htab
  exact hderiv t (ht.mpr htab)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContDiffOn
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.norm_sub_le_integral_of_inner_deriv_le then
    throwError "Refusing to shadow existing declaration ContDiffOn.norm_sub_le_integral_of_inner_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.norm_sub_le_integral_of_inner_deriv_le ``Submission.ContDiffOn.norm_sub_le_integral_of_inner_deriv_le

end Calculus
end Analysis
end DifferentialGeometry
