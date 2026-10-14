import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderLimitRicci
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Collapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedVolumeUpper
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniformVolumeCollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

private theorem model_radius_buffer (A : ℝ) (hA : 1 ≤ A) :
    let δ := _root_.Min.min (1 / 4) ((A + 1)⁻¹ ^ 2)
    0 < δ ∧ δ ≤ 1 / 4 ∧ A < CanonicalNeighborhood.modelRadius δ := by
  intro δ
  have ha : 0 < A + 1 := by linarith
  have hδ : 0 < δ := lt_min (by norm_num) (sq_pos_of_pos (inv_pos.mpr ha))
  refine ⟨hδ, min_le_left _ _, ?_⟩
  have hanti := CanonicalNeighborhood.modelRadius_anti hδ (min_le_right (1 / 4) ((A + 1)⁻¹ ^ 2))
  have heq : CanonicalNeighborhood.modelRadius ((A + 1)⁻¹ ^ 2) = A + 1 := by
    rw [CanonicalNeighborhood.modelRadius, Real.sqrt_sq (inv_nonneg.mpr ha.le), inv_inv]
  rw [heq] at hanti
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.model_radius_buffer
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.model_radius_buffer target :: scope.openDecls } }

theorem exists_standard_high_scalar_small_volume
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ A Q₀ : ℝ, 0 < A ∧ 0 < Q₀ ∧
      ∀ (S : PartialStandardSolution) (x : E3) (t : ℝ),
        t ∈ S.domain → τ ≤ t → t < 1 → Q₀ ≤ metricScalarAt (S.metric t) x →
        riemannianVolumeMeasure (𝓡 3) E3 (S.metric t)
          (riemannianBallOf (S.metric t) x (A / Real.sqrt (metricScalarAt (S.metric t) x))) ≤
            ENNReal.ofReal ε * ENNReal.ofReal ((A / Real.sqrt (metricScalarAt (S.metric t) x)) ^ 3) := by
  let κ := standardModelKappa
  obtain ⟨B, hB, hcollapse⟩ := KappaSolutions.exists_normalized_ancient_kappa_volume_collapse_radius
    κ (ε / 81) (by positivity)
  let A := B / 3
  have hA : 0 < A := div_pos (by linarith) (by norm_num)
  let δ := _root_.Min.min (1 / 4) ((B + 1)⁻¹ ^ 2)
  obtain ⟨hδ, hδ4, hbuffer⟩ := model_radius_buffer B hB
  obtain ⟨Q₀, hQ₀, hmodel⟩ := exists_standard_high_scalar_model hδ
    (hδ4.trans_lt (by norm_num)) hτ
  refine ⟨A, Q₀, hA, hQ₀, ?_⟩
  intro S x t ht hτt ht1 hQ
  obtain ⟨W⟩ := hmodel S x t ht hτt ht1 hQ
  have h3A : 3 * A = B := by dsimp only [A]; ring
  have hvol := W.normalized_ball_volume_le hδ4 hA (by rw [h3A]; exact hbuffer.le)
  have hm := hcollapse W.model W.model_ancient W.model_scalar_base
  rw [h3A] at hvol
  have hnorm : riemannianVolumeMeasure (𝓡 3) E3
      (rescaledMetric S.toSolutionOn t (S.toSolutionOn.scalar t x) W.scalar_pos 0)
        (riemannianBallOf (rescaledMetric S.toSolutionOn t (S.toSolutionOn.scalar t x) W.scalar_pos 0) x A) ≤
      ENNReal.ofReal ε * ENNReal.ofReal (A ^ 3) := by
    refine hvol.trans ((mul_le_mul' (le_refl (3 : ℝ≥0∞)) hm).trans_eq ?_)
    rw [← ENNReal.ofReal_ofNat (3 : ℕ), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hε.le]
    congr 1
    dsimp only [A]
    ring
  let Q := metricScalarAt (S.metric t) x
  have hQpos : 0 < Q := hQ₀.trans_le hQ
  have hmetric : rescaledMetric S.toSolutionOn t (S.toSolutionOn.scalar t x) W.scalar_pos 0 =
      scaleMetric Q hQpos (S.metric t) := by
    simp only [rescaledMetric, parabolicTime_zero]
    rfl
  have hball : riemannianBallOf (scaleMetric Q hQpos (S.metric t)) x A =
      riemannianBallOf (S.metric t) x (A / Real.sqrt Q) := by
    simpa only [mul_div_cancel₀ A (Real.sqrt_pos.mpr hQpos).ne'] using
      KappaSolutions.riemannianBallOf_scaleMetric (S.metric t) Q hQpos x (A / Real.sqrt Q)
  rw [hmetric, hball, volume_scale_apply] at hnorm
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hnorm
  have hsplit : ENNReal.ofReal (A ^ 3) =
      ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q), ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      mul_div_cancel₀ A (Real.sqrt_pos.mpr hQpos).ne']
  rw [hsplit] at hnorm
  apply (ENNReal.mul_le_mul_iff_right
    (pow_ne_zero 3 (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQpos)).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
  exact hnorm.trans_eq (by ac_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_high_scalar_small_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_high_scalar_small_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_high_scalar_small_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_high_scalar_small_volume

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3 : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3 target :: scope.openDecls } }

theorem standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top
    {ι : Type*} {l : Filter ι}
    (S : ι → PartialStandardSolution) (x : ι → E3) (t : ι → ℝ)
    (ht : ∀ i, t i ∈ (S i).domain) {τ : ℝ} (hτ : 0 < τ)
    (hlate : ∀ᶠ i in l, τ ≤ t i ∧ t i < 1)
    (hscalar : _root_.Filter.Tendsto (fun i => metricScalarAt ((S i).metric (t i)) (x i)) l _root_.Filter.atTop)
    {D : ℝ} (hD : 0 < D) :
    _root_.Filter.Tendsto (fun i => riemannianVolumeMeasure (𝓡 3) E3 ((S i).metric (t i))
      (riemannianBallOf ((S i).metric (t i)) (x i) D)) l (𝓝 0) := by
  apply tendsto_riemannianBallOf_volume_zero_of_small_rescaled_balls
    (fun _ : ι => E3) (fun i => (S i).metric (t i))
    (fun i => (S i).complete (t i) (ht i))
    (fun i y v => by
      rw [_root_.MulZeroClass.zero_mul]
      exact (S i).ricciTensor_nonnegative (t i) (ht i) y v)
    x hscalar (hD := hD)
  intro ε hε
  obtain ⟨A, Q₀, hA, _, hsmall⟩ := exists_standard_high_scalar_small_volume hτ hε
  refine ⟨A, hA, ?_⟩
  filter_upwards [hlate, hscalar.eventually_ge_atTop Q₀] with i hi hQ
  have hv := hsmall (S i) (x i) (t i) (ht i) hi.1 hi.2 hQ
  simpa only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_mul hε.le] using hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top

theorem standard_fixed_radius_volume_tendsto_zero_of_time_tendsto
    {ι : Type*} {l : Filter ι}
    (S : ι → PartialStandardSolution) (x : ι → E3) (t : ι → ℝ)
    (ht : ∀ i, t i ∈ (S i).domain) {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (htend : _root_.Filter.Tendsto t l (𝓝 T))
    (hscalar : _root_.Filter.Tendsto (fun i => metricScalarAt ((S i).metric (t i)) (x i)) l _root_.Filter.atTop)
    {D : ℝ} (hD : 0 < D) :
    _root_.Filter.Tendsto (fun i => riemannianVolumeMeasure (𝓡 3) E3 ((S i).metric (t i))
      (riemannianBallOf ((S i).metric (t i)) (x i) D)) l (𝓝 0) := by
  apply standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top S x t ht (half_pos hT)
    (hscalar := hscalar) (hD := hD)
  have hevent : ∀ᶠ i in l, t i ∈ _root_.Set.Ioo (T / 2) 1 :=
    htend (Ioo_mem_nhds (half_lt_self hT) hT1)
  filter_upwards [hevent] with i hi
  exact ⟨hi.1.le, hi.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_time_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_time_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_time_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_fixed_radius_volume_tendsto_zero_of_time_tendsto

end DifferentialGeometry.PDE.RicciFlow
