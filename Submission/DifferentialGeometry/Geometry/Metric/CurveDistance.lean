import Submission.DifferentialGeometry.Geometry.Metric.CurveLength
import Submission.DifferentialGeometry.Geometry.Metric.ScalarCurveComparison
import Submission.DifferentialGeometry.Analysis.Calculus.Variation.Lipschitz
import Submission.DifferentialGeometry.Topology.Connected.FiniteEDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianDistance_le_curveLength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    {a b : ℝ} (hab : a ≤ b) :
    (riemannianEDistOf g (γ a) (γ b)).toReal ≤ riemannianCurveLength g γ a b := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hγ' : LipschitzWith C γ := hγ
  let ν : ℝ → ℝ := fun t => _root_.Dist.dist (γ a) (γ t)
  have hν : LipschitzWith C ν := by
    simpa only [one_mul, ν, Function.comp_def] using! (LipschitzWith.dist_right (γ a)).comp hγ'
  have hνac := hν.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hae : ∀ᵐ t ∂volume, deriv ν t ≤ riemannianCurveSpeed g γ t := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hν.ae_differentiableAt_real]
      with t ht hνt
    apply (le_abs_self _).trans (abs_deriv_le_of_riemannian_distance_bound g ht hνt ?_)
    intro y
    change |_root_.Dist.dist (γ a) (γ y) - _root_.Dist.dist (γ a) (γ t)| ≤ (_root_.EDist.edist (γ t) (γ y)).toReal
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    simpa only [dist_comm] using abs_dist_sub_le (γ y) (γ t) (γ a)
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Set.uIcc a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using ((isCompact_uIcc : IsCompact (_root_.Set.uIcc a b)).measure_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume))⟩
  have hspeed : IntervalIntegrable (riemannianCurveSpeed g γ) _root_.MeasureTheory.MeasureSpace.volume a b :=
    (integrableOn_riemannianCurveSpeed g hγ (_root_.Set.uIcc a b)).intervalIntegrable
  have hle := intervalIntegral.integral_mono_ae hab hνac.intervalIntegrable_deriv hspeed hae
  rw [hνac.integral_deriv_eq_sub] at hle
  have hlen : (∫ t in a..b, riemannianCurveSpeed g γ t) = riemannianCurveLength g γ a b := by
    rw [riemannianCurveLength_eq_integral g hγ,
      intervalIntegral.integral_of_le hab, _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hlen] at hle
  change (_root_.EDist.edist (γ a) (γ b)).toReal ≤ _
  simpa only [ν, dist_self, sub_zero, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDistance_le_curveLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDistance_le_curveLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDistance_le_curveLength ``Submission.DifferentialGeometry.Geometry.riemannianDistance_le_curveLength

end DifferentialGeometry.Geometry
