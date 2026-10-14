import Submission.DifferentialGeometry.Analysis.SpecialFunctions.Sqrt.GramDeterminant
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Continuity
import Submission.DifferentialGeometry.Geometry.Measure.Area.Manifold
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Regularization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def regularizedPullbackAreaDensity (g : SmoothRiemannianMetric I M) (q : ℂ → M)
    (δ : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt ((pullbackMetricCoefficients g q z 1 1 + δ) *
    (pullbackMetricCoefficients g q z Complex.I Complex.I + δ) -
      (pullbackMetricCoefficients g q z 1 Complex.I) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedPullbackAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity ``Submission.DifferentialGeometry.Geometry.regularizedPullbackAreaDensity

theorem regularizedPullbackAreaDensity_zero (g : SmoothRiemannianMetric I M) (q : ℂ → M) :
    regularizedPullbackAreaDensity g q 0 = riemannianAreaDensity g q := by
  funext z
  simp only [regularizedPullbackAreaDensity, add_zero, riemannianAreaDensity, tangentTwoJacobian,
    pullbackMetricCoefficients_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_zero ``Submission.DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_zero

theorem regularizedPullbackAreaDensity_sub_le
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 ≤ δ) (z : ℂ) :
    0 ≤ regularizedPullbackAreaDensity g q δ z - riemannianAreaDensity g q z ∧
      regularizedPullbackAreaDensity g q δ z - riemannianAreaDensity g q z ≤
        Real.sqrt (δ * (pullbackMetricCoefficients g q z 1 1 +
          pullbackMetricCoefficients g q z Complex.I Complex.I) + δ ^ 2) := by
  have hgram := tangentTwoJacobian_sq g
    (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I)
  apply Real.sqrt_regularized_gram_sub_le
    (metric_inner_self_nonneg g (q z) _) (metric_inner_self_nonneg g (q z) _) _ hδ
  have hs := sq_nonneg (tangentTwoJacobian g
    (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I))
  rw [hgram] at hs
  exact sub_nonneg.mp hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_sub_le ``Submission.DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_sub_le

theorem continuousOn_regularizedPullbackAreaDensity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) (δ : ℝ) :
    ContinuousOn (regularizedPullbackAreaDensity g q δ) Ω := by
  have hc := continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hΩ hq
  apply ContinuousOn.sqrt
  have h1 := (hc.clm_apply (continuousOn_const (c := (1 : ℂ)))).clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  exact ((h1.add continuousOn_const).mul
    (((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).add continuousOn_const)).sub
      (((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_regularizedPullbackAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_regularizedPullbackAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_regularizedPullbackAreaDensity ``Submission.DifferentialGeometry.Geometry.continuousOn_regularizedPullbackAreaDensity

theorem exists_uniform_regularizedPullbackAreaDensity_bound
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ z ∈ K,
      |regularizedPullbackAreaDensity g q δ z - riemannianAreaDensity g q z| ≤ C * Real.sqrt δ := by
  let A := pullbackMetricCoefficients g q
  have hc := continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hΩ hq
  have ht : ContinuousOn (fun z => A z 1 1 + A z Complex.I Complex.I) K :=
    (((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).add
      ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)).mono hKΩ
  obtain ⟨B, hB⟩ := hK.bddAbove_image ht
  refine ⟨Real.sqrt (B + 1), Real.sqrt_nonneg _, ?_⟩
  intro δ hδ z hz
  have hgram := tangentTwoJacobian_sq g
    (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I)
  have hdet : (A z 1 Complex.I) ^ 2 ≤ A z 1 1 * A z Complex.I Complex.I := by
    have hs := sq_nonneg (tangentTwoJacobian g
      (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I))
    rw [hgram] at hs
    exact sub_nonneg.mp hs
  have hh := Real.sqrt_regularized_gram_sub_le_of_trace_le
    (metric_inner_self_nonneg g (q z) (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)))
    (metric_inner_self_nonneg g (q z) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I))
    hdet hδ.1 hδ.2 (hB (_root_.Set.mem_image_of_mem _ hz))
  simpa only [regularizedPullbackAreaDensity, riemannianAreaDensity, tangentTwoJacobian,
    A, pullbackMetricCoefficients_apply, mul_comm] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_regularizedPullbackAreaDensity_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_regularizedPullbackAreaDensity_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_regularizedPullbackAreaDensity_bound ``Submission.DifferentialGeometry.Geometry.exists_uniform_regularizedPullbackAreaDensity_bound

theorem tendsto_integral_regularizedPullbackAreaDensity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    _root_.Filter.Tendsto (fun δ : ℝ => ∫ z in K, regularizedPullbackAreaDensity g q δ z)
      (𝓝[≥] (0 : ℝ)) (𝓝 (riemannianArea g q K)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_regularizedPullbackAreaDensity_bound g hΩ hq hK hKΩ
  have hI (δ : ℝ) : _root_.MeasureTheory.IntegrableOn (regularizedPullbackAreaDensity g q δ) K :=
    ((continuousOn_regularizedPullbackAreaDensity g hΩ hq δ).mono hKΩ).integrableOn_compact hK
  have harea : _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity g q) K :=
    integrableOn_riemannianAreaDensity_of_contMDiffOn g hΩ hq hK hKΩ
  have hδ : ∀ᶠ δ : ℝ in 𝓝[≥] (0 : ℝ), δ ∈ _root_.Set.Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with δ h0 h1
    exact ⟨h0, h1.le⟩
  have hnorm : ∀ᶠ δ : ℝ in 𝓝[≥] (0 : ℝ),
      ‖(∫ z in K, regularizedPullbackAreaDensity g q δ z) - riemannianArea g q K‖ ≤
        C * Real.sqrt δ * volume.real K := by
    filter_upwards [hδ] with δ hδ
    rw [riemannianArea, ← _root_.MeasureTheory.integral_sub (hI δ) harea]
    exact _root_.MeasureTheory.norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun z hz => by
      simpa only [Real.norm_eq_abs] using hbound δ hδ z hz)
  have hlim : _root_.Filter.Tendsto (fun δ : ℝ => C * Real.sqrt δ * volume.real K)
      (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    have hs : _root_.Filter.Tendsto Real.sqrt (𝓝[≥] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := hs.const_mul C
    simpa only [Real.sqrt_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul] using hh.mul_const (volume.real K)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hnorm hlim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tendsto_integral_regularizedPullbackAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tendsto_integral_regularizedPullbackAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tendsto_integral_regularizedPullbackAreaDensity ``Submission.DifferentialGeometry.Geometry.tendsto_integral_regularizedPullbackAreaDensity

theorem exists_pos_integral_regularizedPullbackAreaDensity_lt
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (∫ z in K, regularizedPullbackAreaDensity g q δ z) < riemannianArea g q K + ε := by
  have hlim := (tendsto_integral_regularizedPullbackAreaDensity g hΩ hq hK hKΩ).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) from nhdsWithin_mono _ _root_.Set.Ioi_subset_Ici_self)
  have hh := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, harea⟩ := (hpos.and hh).exists
  exact ⟨δ, hδ, harea⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_pos_integral_regularizedPullbackAreaDensity_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_pos_integral_regularizedPullbackAreaDensity_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_pos_integral_regularizedPullbackAreaDensity_lt ``Submission.DifferentialGeometry.Geometry.exists_pos_integral_regularizedPullbackAreaDensity_lt

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem regularizedPullbackAreaDensity_eq_sqrt_metric_gram
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} (Ω : TopologicalSpace.Opens ℂ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω) (δ : ℝ)
    (heq : ∀ (x : Ω) (v w : ℂ), h.inner x v w =
      pullbackMetricCoefficients g q x.1 v w + δ * _root_.Inner.inner ℝ v w) (z : Ω) :
    regularizedPullbackAreaDensity g q δ z.1 =
      Real.sqrt (h.inner z (1 : ℂ) (1 : ℂ) * h.inner z Complex.I Complex.I -
        h.inner z (1 : ℂ) Complex.I ^ 2) := by
  rw [heq, heq, heq]
  norm_num [regularizedPullbackAreaDensity, Complex.inner, RCLike.inner_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_eq_sqrt_metric_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_eq_sqrt_metric_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_eq_sqrt_metric_gram ``Submission.DifferentialGeometry.Geometry.regularizedPullbackAreaDensity_eq_sqrt_metric_gram

theorem exists_regularized_pullback_disk_metric_area_lt
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} (Ω : TopologicalSpace.Opens ℂ)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω)
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω), 0 < δ ∧
      (∀ (x : Ω) (v w : ℂ), h.inner x v w =
        pullbackMetricCoefficients g q x.1 v w + δ * _root_.Inner.inner ℝ v w) ∧
      (∀ (x : Ω) (v : ℂ), δ * ‖v‖ ^ 2 ≤ h.inner x v v) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g q δ z) <
        riemannianArea g q (Metric.closedBall 0 1) + ε := by
  obtain ⟨δ, hδ, harea⟩ := exists_pos_integral_regularizedPullbackAreaDensity_lt
    g Ω.isOpen (hq.of_le (by norm_cast)) (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1) hD hε
  obtain ⟨h, heq, hbound⟩ := exists_smoothMetric_regularized_pullback g Ω hq hδ
  exact ⟨δ, h, hδ, heq, hbound, harea⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_regularized_pullback_disk_metric_area_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_regularized_pullback_disk_metric_area_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_regularized_pullback_disk_metric_area_lt ``Submission.DifferentialGeometry.Geometry.exists_regularized_pullback_disk_metric_area_lt

end DifferentialGeometry.Geometry

end

end
