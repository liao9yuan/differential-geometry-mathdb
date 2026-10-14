import Submission.DifferentialGeometry.Analysis.Integration.Integral.CompactSupportDerivative
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.SupportMargin
import Mathlib.Analysis.Complex.CauchyIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Metric _root_.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff _root_.ComplexConjugate _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis



def diskImageComplexPotential (κ : ℂ → ℝ) (z : ℂ) : ℂ :=
  ∫ w : ℂ, (κ w : ℂ) * Complex.log (1 - conj w * z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskImageComplexPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskImageComplexPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskImageComplexPotential ``Submission.DifferentialGeometry.Analysis.diskImageComplexPotential


def diskImageComplexDerivative (κ : ℂ → ℝ) (z w : ℂ) : ℂ :=
  (κ w : ℂ) * ((1 - conj w * z)⁻¹ * (-conj w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskImageComplexDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskImageComplexDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskImageComplexDerivative ``Submission.DifferentialGeometry.Analysis.diskImageComplexDerivative



theorem diskImageComplexKernel_argument_mem_slitPlane {w z : ℂ}
    (h : ‖w‖ * ‖z‖ < 1) : 1 - conj w * z ∈ Complex.slitPlane := by
  have hn : ‖-(conj w * z)‖ < 1 := by
    simpa only [norm_neg, norm_mul, Complex.norm_conj] using h
  simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskImageComplexKernel_argument_mem_slitPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskImageComplexKernel_argument_mem_slitPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskImageComplexKernel_argument_mem_slitPlane ``Submission.DifferentialGeometry.Analysis.diskImageComplexKernel_argument_mem_slitPlane


theorem hasDerivAt_weighted_diskImageComplexKernel {κ : ℂ → ℝ} {w z : ℂ}
    (h : ‖w‖ * ‖z‖ < 1) :
    HasDerivAt (fun q : ℂ => (κ w : ℂ) * Complex.log (1 - conj w * q))
      (diskImageComplexDerivative κ z w) z := by
  have harg := ((hasDerivAt_id z).const_mul (conj w)).const_sub 1
  have hlog := (Complex.hasDerivAt_log
    (diskImageComplexKernel_argument_mem_slitPlane h)).comp z harg
  simpa only [diskImageComplexDerivative, Function.comp_apply, id_eq, neg_mul, mul_one] using!
    HasDerivAt.const_mul (κ w : ℂ) hlog

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_weighted_diskImageComplexKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_weighted_diskImageComplexKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_weighted_diskImageComplexKernel ``Submission.DifferentialGeometry.Analysis.hasDerivAt_weighted_diskImageComplexKernel



theorem continuousOn_weighted_diskImageComplexKernel {κ : ℂ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) :
    ContinuousOn
      (fun q : ℂ × ℂ => (κ q.2 : ℂ) * Complex.log (1 - conj q.2 * q.1))
      (Metric.ball (0 : ℂ) R ×ˢ _root_.Set.univ) := by
  intro q hq
  by_cases hw : q.2 ∈ tsupport κ
  · have hp : ‖q.2‖ * ‖q.1‖ < 1 :=
      (mul_le_mul_of_nonneg_right (hs q.2 hw) (norm_nonneg q.1)).trans_lt
        ((mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hq.1) hρ).trans hρR)
    have harg : ContinuousAt (fun p : ℂ × ℂ => 1 - conj p.2 * p.1) q := by fun_prop
    have hlog : ContinuousAt (fun p : ℂ × ℂ => Complex.log (1 - conj p.2 * p.1)) q :=
      harg.clog (diskImageComplexKernel_argument_mem_slitPlane hp)
    have hsource : ContinuousAt (fun p : ℂ × ℂ => (κ p.2 : ℂ)) q :=
      Complex.continuous_ofReal.continuousAt.comp
        (hκ.continuous.continuousAt.comp continuousAt_snd)
    exact (hsource.mul hlog).continuousWithinAt
  · have he : (fun p : ℂ × ℂ =>
        (κ p.2 : ℂ) * Complex.log (1 - conj p.2 * p.1)) =ᶠ[𝓝 q] 0 := by
      have hn : ∀ᶠ p : ℂ × ℂ in 𝓝 q, p.2 ∉ tsupport κ :=
        ((isClosed_tsupport κ).isOpen_compl.preimage continuous_snd).mem_nhds hw
      filter_upwards [hn] with p hp
      have hk : κ p.2 = 0 := by
        by_contra hne
        exact hp (subset_closure hne)
      simp only [hk, Complex.ofReal_zero, _root_.MulZeroClass.zero_mul, Pi.zero_apply]
    exact (continuousAt_const.congr_of_eventuallyEq he).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_weighted_diskImageComplexKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_weighted_diskImageComplexKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_weighted_diskImageComplexKernel ``Submission.DifferentialGeometry.Analysis.continuousOn_weighted_diskImageComplexKernel


theorem continuousOn_diskImageComplexDerivative {κ : ℂ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) :
    ContinuousOn (fun q : ℂ × ℂ => diskImageComplexDerivative κ q.1 q.2)
      (Metric.ball (0 : ℂ) R ×ˢ _root_.Set.univ) := by
  intro q hq
  by_cases hw : q.2 ∈ tsupport κ
  · have hp : ‖q.2‖ * ‖q.1‖ < 1 :=
      (mul_le_mul_of_nonneg_right (hs q.2 hw) (norm_nonneg q.1)).trans_lt
        ((mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hq.1) hρ).trans hρR)
    have hne : 1 - conj q.2 * q.1 ≠ 0 := diskImageLogKernel_argument_ne_zero hp
    have hsource : ContinuousAt (fun p : ℂ × ℂ => (κ p.2 : ℂ)) q :=
      Complex.continuous_ofReal.continuousAt.comp
        (hκ.continuous.continuousAt.comp continuousAt_snd)
    have hden : ContinuousAt (fun p : ℂ × ℂ => 1 - conj p.2 * p.1) q := by fun_prop
    have hnum : ContinuousAt (fun p : ℂ × ℂ => -conj p.2) q := by fun_prop
    exact (hsource.mul (hden.inv₀ hne |>.mul hnum)).continuousWithinAt
  · have he : (fun p : ℂ × ℂ => diskImageComplexDerivative κ p.1 p.2) =ᶠ[𝓝 q] 0 := by
      have hn : ∀ᶠ p : ℂ × ℂ in 𝓝 q, p.2 ∉ tsupport κ :=
        ((isClosed_tsupport κ).isOpen_compl.preimage continuous_snd).mem_nhds hw
      filter_upwards [hn] with p hp
      have hk : κ p.2 = 0 := by
        by_contra hne
        exact hp (subset_closure hne)
      simp only [diskImageComplexDerivative, hk, Complex.ofReal_zero, _root_.MulZeroClass.zero_mul, Pi.zero_apply]
    exact (continuousAt_const.congr_of_eventuallyEq he).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_diskImageComplexDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_diskImageComplexDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_diskImageComplexDerivative ``Submission.DifferentialGeometry.Analysis.continuousOn_diskImageComplexDerivative



theorem differentiableOn_diskImageComplexPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) :
    DifferentiableOn ℂ (diskImageComplexPotential κ) (Metric.ball (0 : ℂ) R) := by
  intro z hz
  have hd := hasDerivAt_planeIntegral_of_compact_support_rclike
    (𝕜 := ℂ)
    (f := fun z w => (κ w : ℂ) * Complex.log (1 - conj w * z))
    (f' := diskImageComplexDerivative κ)
    _root_.Metric.isOpen_ball hc
    (fun _ w _ hw => by
      have hk : κ w = 0 := by
        by_contra hne
        exact hw (subset_closure hne)
      simp only [hk, Complex.ofReal_zero, _root_.MulZeroClass.zero_mul])
    (continuousOn_weighted_diskImageComplexKernel hκ hρ hρR hs)
    (continuousOn_diskImageComplexDerivative hκ hρ hρR hs)
    (fun q hq w => by
      by_cases hw : w ∈ tsupport κ
      · apply hasDerivAt_weighted_diskImageComplexKernel
        exact (mul_le_mul_of_nonneg_right (hs w hw) (norm_nonneg q)).trans_lt
          ((mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hq) hρ).trans hρR)
      · have hk : κ w = 0 := by
          by_contra hne
          exact hw (subset_closure hne)
        simpa only [hk, Complex.ofReal_zero, _root_.MulZeroClass.zero_mul, diskImageComplexDerivative] using
          hasDerivAt_const q (0 : ℂ))
    hz
  exact hd.differentiableAt.differentiableWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.differentiableOn_diskImageComplexPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.differentiableOn_diskImageComplexPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.differentiableOn_diskImageComplexPotential ``Submission.DifferentialGeometry.Analysis.differentiableOn_diskImageComplexPotential



theorem integrable_weighted_diskImageComplexKernel {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    Integrable (fun w : ℂ => (κ w : ℂ) * Complex.log (1 - conj w * z)) := by
  have hcont : Continuous (fun w : ℂ => (κ w : ℂ) * Complex.log (1 - conj w * z)) := by
    rw [← continuousOn_univ]
    exact (continuousOn_weighted_diskImageComplexKernel hκ hρ hρR hs).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hz, _root_.Set.mem_univ _⟩)
  apply hcont.integrable_of_hasCompactSupport
  exact HasCompactSupport.intro hc fun w hw => by
    have hk : κ w = 0 := by
      by_contra hne
      exact hw (subset_closure hne)
    simp only [hk, Complex.ofReal_zero, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_weighted_diskImageComplexKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_weighted_diskImageComplexKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_weighted_diskImageComplexKernel ``Submission.DifferentialGeometry.Analysis.integrable_weighted_diskImageComplexKernel



theorem diskImagePotential_eq_re_diskImageComplexPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    diskImagePotential κ z =
      -(1 / (2 * Real.pi)) * (diskImageComplexPotential κ z).re := by
  rw [diskImagePotential, diskImageComplexPotential]
  congr 1
  calc
    ∫ w : ℂ, κ w * diskImageLogKernel w z =
        ∫ w : ℂ, ((κ w : ℂ) * Complex.log (1 - conj w * z)).re := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with w
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, _root_.MulZeroClass.zero_mul, sub_zero,
        Complex.log_re, diskImageLogKernel]
    _ = (∫ w : ℂ, (κ w : ℂ) * Complex.log (1 - conj w * z)).re :=
      integral_re (integrable_weighted_diskImageComplexKernel hc hκ hρ hρR hs hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskImagePotential_eq_re_diskImageComplexPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskImagePotential_eq_re_diskImageComplexPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskImagePotential_eq_re_diskImageComplexPotential ``Submission.DifferentialGeometry.Analysis.diskImagePotential_eq_re_diskImageComplexPotential



theorem harmonicAt_diskImagePotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    HarmonicAt (diskImagePotential κ) z := by
  have hanalytic : AnalyticAt ℂ (diskImageComplexPotential κ) z :=
    (differentiableOn_diskImageComplexPotential hc hκ hρ hρR hs).analyticAt
      (isOpen_ball.mem_nhds hz)
  have heq : Filter.EventuallyEq (nhds z) (diskImagePotential κ)
      (-(1 / (2 * Real.pi)) • fun q : ℂ => (diskImageComplexPotential κ q).re) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with q hq
    simpa only [Pi.smul_apply, smul_eq_mul] using
      diskImagePotential_eq_re_diskImageComplexPotential hc hκ hρ hρR hs hq
  exact (_root_.InnerProductSpace.harmonicAt_congr_nhds heq).2
    (hanalytic.harmonicAt_re.const_smul (c := -(1 / (2 * Real.pi))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.harmonicAt_diskImagePotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.harmonicAt_diskImagePotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.harmonicAt_diskImagePotential ``Submission.DifferentialGeometry.Analysis.harmonicAt_diskImagePotential


theorem laplacian_diskImagePotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    Laplacian.laplacian (diskImagePotential κ) z = 0 :=
  (harmonicAt_diskImagePotential hc hκ hρ hρR hs hz).2.self_of_nhds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_diskImagePotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_diskImagePotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_diskImagePotential ``Submission.DifferentialGeometry.Analysis.laplacian_diskImagePotential



theorem exists_harmonicOnNhd_diskImagePotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧ _root_.InnerProductSpace.HarmonicOnNhd (diskImagePotential κ) (Metric.ball (0 : ℂ) R) := by
  obtain ⟨ρ, R, hρ, _, hR, hρR, hsρ⟩ := exists_disk_support_radii hc hs
  exact ⟨R, hR, fun _ hz => harmonicAt_diskImagePotential hc hκ hρ hρR hsρ hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_harmonicOnNhd_diskImagePotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_harmonicOnNhd_diskImagePotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_harmonicOnNhd_diskImagePotential ``Submission.DifferentialGeometry.Analysis.exists_harmonicOnNhd_diskImagePotential

end DifferentialGeometry.Analysis
