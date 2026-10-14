import Submission.DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskIsotopyDensity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskIsotopyIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem SmoothDiskExtension.hasDerivAt_area_isotopy_flux
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ _root_.Set.univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension (G t₀) U z = 0) :
    let W := fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t₀ 1
    let b := fun θ => (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
        Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      IntervalIntegrable b _root_.MeasureTheory.MeasureSpace.volume (-Real.pi) Real.pi ∧
      HasDerivAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
        ((∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
          ∫ θ in -Real.pi..Real.pi, b θ) t₀ := by
  dsimp only
  obtain ⟨s, hs, hDs, hU⟩ := hu.2
  let W : ∀ q, TangentSpace 𝓘(ℝ, E) (U q) :=
    fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t₀ 1
  have hW := contMDiffOn_isotopyDiskVelocity hT hT₀ hΦ hΦ₀ hs hU
  have hmetric := (hu.hasDerivAt_area_metric hG ht₀ hconf).1
  have hdiv := integrableOn_diskMapSectionDivergence (G t₀) hs hU hDs hharm hW
  have hboundary := continuous_diskMapSectionInwardFlux (G t₀) hs hU
    (Metric.sphere_subset_closedBall.trans hDs)
    (fun z hz => hconf z (Metric.sphere_subset_closedBall hz)) hW
  have hflux := integral_diskMapSectionDivergence (G t₀) hs hU hDs hconf hharm hW
  have heq :
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskMapMetricVariationDensity (fun r => Diffeomorph.pullbackMetric (G r) (Φ r)) t₀ U z) =
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
        ∫ θ in -Real.pi..Real.pi,
          (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
            (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
              Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ)) := by
    calc
      _ = ∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationDensity G t₀ U z + diskMapSectionDivergence (G t₀) U W z := by
        apply _root_.MeasureTheory.setIntegral_congr_fun measurableSet_closedBall
        intro z hz
        exact diskMapMetricVariationDensity_pullback hG ht₀ hT hT₀ hΦ hΦ₀ hs hU (hDs hz)
      _ = _ := by
        rw [_root_.MeasureTheory.integral_add hmetric hdiv, hflux]
        rfl
  have hd := (hu.hasDerivAt_area_isotopy hG ht₀ hT hT₀ hΦ hΦ₀ hconf).2
  rw [heq] at hd
  exact ⟨hmetric, hboundary.intervalIntegrable _ _, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy_flux ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy_flux

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem SmoothDiskExtension.hasDerivWithinAt_area_isotopy_flux_on_Icc
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ}
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {a b : ℝ}
    (hT₀ : t₀ ∈ _root_.Set.Ico a b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension (G t₀) U z = 0) :
    let W := fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (_root_.Set.Icc a b) t₀ 1
    let beta := fun θ => (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
        Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ))
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationDensity G t₀ U) (Metric.closedBall 0 1) ∧
      IntervalIntegrable beta _root_.MeasureTheory.MeasureSpace.volume (-Real.pi) Real.pi ∧
      HasDerivWithinAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
        ((∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
          ∫ θ in -Real.pi..Real.pi, beta θ) (_root_.Set.Icc a b) t₀ := by
  have hab : a < b := lt_of_le_of_lt hT₀.1 hT₀.2
  have ht₀ : D.regular ∈ 𝓝 t₀ := D.regular_isOpen.mem_nhds (hreg ⟨hT₀.1, hT₀.2.le⟩)
  dsimp only
  obtain ⟨s, hs, hDs, hU⟩ := hu.2
  let W : ∀ q, TangentSpace 𝓘(ℝ, E) (U q) :=
    fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (_root_.Set.Icc a b) t₀ 1
  have hW := contMDiffOn_isotopyDiskVelocityWithin (uniqueDiffOn_Icc hab)
    ⟨hT₀.1, hT₀.2.le⟩ hΦ hΦ₀ hU
  have hmetric := (hu.hasDerivAt_area_metric hG ht₀ hconf).1
  have hdiv := integrableOn_diskMapSectionDivergence (G t₀) hs hU hDs hharm hW
  have hboundary := continuous_diskMapSectionInwardFlux (G t₀) hs hU
    (Metric.sphere_subset_closedBall.trans hDs)
    (fun z hz => hconf z (Metric.sphere_subset_closedBall hz)) hW
  have hflux := integral_diskMapSectionDivergence (G t₀) hs hU hDs hconf hharm hW
  have heq :
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskMapMetricVariationWithinDensity (fun r => Diffeomorph.pullbackMetric (G r) (Φ r))
          (_root_.Set.Icc a b) t₀ U z) =
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity G t₀ U z) -
        ∫ θ in -Real.pi..Real.pi,
          (G t₀).inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
            (diskMapInwardConormal (G t₀) U (circleMap 0 1 θ)) *
              Real.sqrt (diskMapConformalCoefficient (G t₀) U (circleMap 0 1 θ)) := by
    calc
      _ = ∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationDensity G t₀ U z + diskMapSectionDivergence (G t₀) U W z := by
        apply _root_.MeasureTheory.setIntegral_congr_fun measurableSet_closedBall
        intro z hz
        exact diskMapMetricVariationWithinDensity_pullback hG ht₀ hab hT₀ hΦ hΦ₀ hs hU (hDs hz)
      _ = _ := by
        rw [_root_.MeasureTheory.integral_add hmetric hdiv, hflux]
        rfl
  have hd := (hu.hasDerivWithinAt_area_isotopy_on_Icc hG hab ⟨hT₀.1, hT₀.2.le⟩ hreg hΦ hΦ₀ hconf).2
  rw [heq] at hd
  exact ⟨hmetric, hboundary.intervalIntegrable _ _, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_flux_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_flux_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_flux_on_Icc ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_flux_on_Icc

end DifferentialGeometry.Geometry

end

end
