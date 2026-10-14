import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation.Basic
import Submission.DifferentialGeometry.Geometry.Metric.CurveDistance
import Submission.DifferentialGeometry.Analysis.Calculus.Variation.Comparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

variable [FiniteDimensional ℝ E] [CompactSpace M] [PreconnectedSpace M]



theorem riemannianCurveVariation_eq_elength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (a b : ℝ) : riemannianCurveVariation g γ a b = riemannianCurveELength g γ a b := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace edist_ne_top_of_preconnected
  have hγ' : LipschitzWith C γ := hγ
  change eVariationOn γ (_root_.Set.Icc a b) = riemannianCurveELength g γ a b
  by_cases hab : a ≤ b
  · have hspeed (x y : ℝ) : IntervalIntegrable (riemannianCurveSpeed g γ) _root_.MeasureTheory.MeasureSpace.volume x y := by
      let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Set.uIcc x y)) :=
        ⟨by simpa only [Measure.restrict_apply_univ] using
          ((isCompact_uIcc : IsCompact (_root_.Set.uIcc x y)).measure_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume))⟩
      exact (integrableOn_riemannianCurveSpeed g hγ (_root_.Set.uIcc x y)).intervalIntegrable
    have hlen (x y : ℝ) (hxy : x ≤ y) :
        (∫ t in x..y, riemannianCurveSpeed g γ t) = riemannianCurveLength g γ x y := by
      rw [riemannianCurveLength_eq_integral g hγ, intervalIntegral.integral_of_le hxy,
        _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
    apply le_antisymm
    · let F : ℝ → ℝ := fun x => ∫ t in a..x, riemannianCurveSpeed g γ t
      have hF (x y : ℝ) : F y - F x = ∫ t in x..y, riemannianCurveSpeed g γ t := by
        have h := intervalIntegral.integral_add_adjacent_intervals (hspeed a x) (hspeed x y)
        dsimp only [F]
        linarith
      have hm : Monotone F := by
        intro x y hxy
        have h := intervalIntegral.integral_nonneg_of_forall (μ := _root_.MeasureTheory.MeasureSpace.volume) hxy (riemannianCurveSpeed_nonneg g γ)
        rw [← hF] at h
        exact sub_nonneg.mp h
      have hbound (x y : ℝ) (hxy : x ≤ y) : _root_.Dist.dist (γ x) (γ y) ≤ F y - F x := by
        rw [hF, hlen x y hxy]
        have h := riemannianDistance_le_curveLength g hγ hxy
        change (_root_.EDist.edist (γ x) (γ y)).toReal ≤ _ at h
        simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
      have hvar := eVariationOn_Icc_le_of_dist_le_sub hm hbound a b
      rw [hF, hlen a b hab, riemannianCurveLength,
        ENNReal.ofReal_toReal (riemannianCurveELength_ne_top_of_lipschitz g hγ a b)] at hvar
      exact hvar
    · let V := variationOnFromTo γ _root_.Set.univ a
      have hV : LipschitzWith C V := lipschitz_variationOnFromTo hγ' a
      have hVac := hV.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
      have hae : ∀ᵐ t ∂volume, riemannianCurveSpeed g γ t ≤ deriv V t := by
        filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hV.ae_differentiableAt_real]
          with t ht hVt
        have hd := riemannianCurveSpeed_le_abs_deriv_of_distance_bound g ht hVt (fun y => by
          have h := dist_le_variationOnFromTo_dist hγ' a t y
          change _root_.EDist.edist (γ t) (γ y) ≤ _
          rw [edist_dist]
          apply ENNReal.ofReal_le_ofReal
          simpa only [V, Real.dist_eq, abs_sub_comm] using h)
        simpa only [V, abs_of_nonneg (deriv_variationOnFromTo_nonneg hγ' a t)] using hd
      have hle := intervalIntegral.integral_mono_ae hab (hspeed a b) hVac.intervalIntegrable_deriv hae
      rw [hlen a b hab, hVac.integral_deriv_eq_sub] at hle
      have hVvalue : V b - V a = (eVariationOn γ (_root_.Set.Icc a b)).toReal := by
        dsimp only [V]
        rw [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le γ _root_.Set.univ hab,
          _root_.Set.univ_inter]
      rw [hVvalue] at hle
      exact (ENNReal.toReal_le_toReal (riemannianCurveELength_ne_top_of_lipschitz g hγ a b)
        (eVariationOn_Icc_ne_top_of_lipschitz hγ' a b)).mp hle
  · simp only [riemannianCurveELength, _root_.Set.Icc_eq_empty_of_lt (lt_of_not_ge hab),
      eVariationOn.subsingleton γ Set.subsingleton_empty, Measure.restrict_empty, _root_.MeasureTheory.lintegral_zero_measure]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveVariation_eq_elength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveVariation_eq_elength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveVariation_eq_elength ``Submission.DifferentialGeometry.Geometry.riemannianCurveVariation_eq_elength


theorem riemannianCurveLength_eq_variation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (a b : ℝ) : riemannianCurveLength g γ a b = (riemannianCurveVariation g γ a b).toReal := by
  rw [riemannianCurveVariation_eq_elength g hγ, riemannianCurveLength]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength_eq_variation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength_eq_variation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength_eq_variation ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength_eq_variation

end DifferentialGeometry.Geometry
