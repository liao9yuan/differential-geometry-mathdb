import Submission.DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation
import Submission.DifferentialGeometry.Geometry.Metric.FamilyTimeBound
import Submission.DifferentialGeometry.Geometry.Measure.Area.MetricDensityError
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Submission.DifferentialGeometry.Analysis.Integration.Integral.ParametricDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem hasDerivAt_integral_diskMapAreaDensity_metric
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) t₀ := by
  let B := Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B := _root_.ProperSpace.isCompact_closedBall _ _
  have hJ (t : ℝ) : ContinuousOn (riemannianAreaDensity (G t) U) s :=
    continuousOn_riemannianAreaDensity (G t) hs (hU.of_le (by simp))
  have hJ0 : _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity (G t₀) U) B :=
    ((hJ t₀).mono hDs).integrableOn_compact hB
  have hder : ContinuousOn (diskMapMetricVariationDensity G t₀ U) B :=
    (contDiffOn_diskMapMetricVariationDensity hG ht₀ hs hU).continuousOn.mono hDs
  obtain ⟨r, K, hr, hK, _, hbounds, hLip⟩ := exists_metricFamily_quadratic_time_bounds hG ht₀
  let bound : ℂ → ℝ := fun z => 4 * K * riemannianAreaDensity (G t₀) U z
  have hbound : _root_.MeasureTheory.IntegrableOn bound B := hJ0.const_mul (4 * K)
  have hloc : ∀ z : ℂ,
      LipschitzOnWith (Real.nnabs (bound z)) (fun t => riemannianAreaDensity (G t) U z) (Metric.ball t₀ r) := by
    intro z
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs'
    have h := riemannianAreaDensity_metric_time_error (G t₀)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2) hK
      (fun t ht x v => (hbounds t ht x v).1) (fun t ht x v => (hbounds t ht x v).2)
      hLip ht hs' U z
    have hn : 0 ≤ bound z := mul_nonneg (mul_nonneg (by norm_num) hK)
      (riemannianAreaDensity_nonneg (G t₀) U z)
    have hecoef : K * 2 / (1 / 2 : ℝ) = 4 * K := by ring
    rw [hecoef] at h
    change |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G s) U z| ≤
      |bound z| * |t - s|
    rw [abs_of_nonneg hn]
    exact h
  exact hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict B)
    (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapMetricVariationDensity G t₀ U) (bound := bound)
    (Metric.ball_mem_nhds t₀ hr)
    (Eventually.of_forall (fun t => ((hJ t).mono hDs).aestronglyMeasurable hB.measurableSet))
    hJ0 (hder.aestronglyMeasurable hB.measurableSet)
    (Eventually.of_forall hloc) hbound
    ((_root_.MeasureTheory.ae_restrict_mem hB.measurableSet).mono
      (fun z hz => hasDerivAt_diskMapAreaDensity_metric hG ht₀ (hconf z hz)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivAt_integral_diskMapAreaDensity_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivAt_integral_diskMapAreaDensity_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivAt_integral_diskMapAreaDensity_metric ``Submission.DifferentialGeometry.Geometry.hasDerivAt_integral_diskMapAreaDensity_metric



theorem SmoothDiskExtension.hasDerivAt_area_metric
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t) u)
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  have h := hasDerivAt_integral_diskMapAreaDensity_metric hG ht₀ hs hU hDs hconf
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) := by
    funext t
    exact riemannianDiskArea_eq_of_extension (G t) u U heq
  rw [he]
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_metric ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_metric

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]

theorem hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ _root_.Set.Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivWithinAt
        (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z)
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U z) (_root_.Set.Icc a b) t₀ := by
  let B := Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B := _root_.ProperSpace.isCompact_closedBall _ _
  have hJ (t : ℝ) : ContinuousOn (riemannianAreaDensity (G t) U) s :=
    continuousOn_riemannianAreaDensity (G t) hs (hU.of_le (by simp))
  have hJ0 : _root_.MeasureTheory.IntegrableOn (riemannianAreaDensity (G t₀) U) B :=
    ((hJ t₀).mono hDs).integrableOn_compact hB
  have hder : ContinuousOn (diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U) B :=
    (contDiffOn_diskMapMetricVariationWithinDensity hab ht₀ hG hs hU).continuousOn.mono hDs
  obtain ⟨r, K, hr, hK, hbounds, hLip⟩ := exists_quadratic_time_bounds_on_Icc hab ht₀ hG
  let bound : ℂ → ℝ := fun z => 4 * K * riemannianAreaDensity (G t₀) U z
  have hbound : _root_.MeasureTheory.IntegrableOn bound B := hJ0.const_mul (4 * K)
  have hloc : ∀ z : ℂ, LipschitzOnWith (Real.nnabs (bound z))
      (fun t => riemannianAreaDensity (G t) U z) (_root_.Set.Icc a b ∩ Metric.ball t₀ r) := by
    intro z
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    have h := riemannianAreaDensity_metric_time_error (G t₀)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2) hK
      (fun t ht x v => (hbounds t ht x v).1) (fun t ht x v => (hbounds t ht x v).2)
      (fun t ht u hu x v => hLip t ht.1 u hu.1 x v) ht hu U z
    have hn : 0 ≤ bound z := mul_nonneg (mul_nonneg (by norm_num) hK)
      (riemannianAreaDensity_nonneg (G t₀) U z)
    have hecoef : K * 2 / (1 / 2 : ℝ) = 4 * K := by ring
    rw [hecoef] at h
    change |riemannianAreaDensity (G t) U z - riemannianAreaDensity (G u) U z| ≤
      |bound z| * |t - u|
    rw [abs_of_nonneg hn]
    exact h
  exact Analysis.Calculus.hasDerivWithinAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict B) (F := fun t z => riemannianAreaDensity (G t) U z)
    (F' := diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U) (bound := bound)
    (uniqueDiffOn_Icc hab t₀ ht₀).accPt
    (_root_.Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hr)))
    ⟨ht₀, Metric.mem_ball_self hr⟩
    (Eventually.of_forall (fun t => ((hJ t).mono hDs).aestronglyMeasurable hB.measurableSet))
    hJ0 (hder.aestronglyMeasurable hB.measurableSet)
    (Eventually.of_forall hloc) hbound
    ((_root_.MeasureTheory.ae_restrict_mem hB.measurableSet).mono
      (fun z hz => hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc hab ht₀ hG (hconf z hz)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc ``Submission.DifferentialGeometry.Geometry.hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc


theorem SmoothDiskExtension.hasDerivWithinAt_area_metric_on_Icc
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ _root_.Set.Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivWithinAt (fun t => riemannianDiskArea (G t) u)
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U z) (_root_.Set.Icc a b) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  have h := hasDerivWithinAt_integral_diskMapAreaDensity_metric_on_Icc hab ht₀ hG hs hU hDs hconf
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) := by
    funext t
    exact riemannianDiskArea_eq_of_extension (G t) u U heq
  rw [he]
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_metric_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_metric_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_metric_on_Icc ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_metric_on_Icc

end DifferentialGeometry.Geometry

end

end
