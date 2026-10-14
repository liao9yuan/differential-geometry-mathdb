import Submission.DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricIntegral
import Submission.DifferentialGeometry.Geometry.Metric.ParameterPullbackFamily
import Submission.DifferentialGeometry.Geometry.Measure.Area.Pullback

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





theorem SmoothDiskExtension.hasDerivAt_area_isotopy
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ _root_.Set.univ))
    (hΦ₀ : Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    let H := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationDensity H t₀ U) (Metric.closedBall 0 1) ∧
      HasDerivAt (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity H t₀ U z) t₀ := by
  let H := fun t => Diffeomorph.pullbackMetric (G t) (Φ t)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (_root_.Filter.inter_mem (hT.mem_nhds hT₀) ht₀)
  have hi : t₀ ∈ _root_.Set.Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - r) (t₀ + r) t₀ hi
  have hsub : D'.carrier ⊆ T ∩ D.regular := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change t₀ - r < t ∧ t < t₀ + r at ht
    constructor <;> linarith [ht.1, ht.2]
  have hH : MetricFamilySmoothOn D' H :=
    metricFamilySmoothOn_parameterPullback hG hT hΦ D' rfl hsub
  have hH₀ : H t₀ = G t₀ := by
    simp only [H, hΦ₀, Diffeomorph.pullbackMetric_refl]
  have hc : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (H t₀) U z := by
    rwa [hH₀]
  have h := hu.hasDerivAt_area_metric hH (isOpen_Ioo.mem_nhds hi) hc
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (H t) u) =
      (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) := by
    funext t
    exact hu.area_pullback (G t) (Φ t)
  rw [he] at h
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivAt_area_isotopy

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem SmoothDiskExtension.hasDerivWithinAt_area_isotopy_on_Icc
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ _root_.Set.Icc a b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    {Phi : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M}
    (hPhi : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Phi p.1 p.2) (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hid : Phi t₀ = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (G t₀) U z) :
    let H := fun t => Diffeomorph.pullbackMetric (G t) (Phi t)
    _root_.MeasureTheory.IntegrableOn (diskMapMetricVariationWithinDensity H (_root_.Set.Icc a b) t₀ U)
        (Metric.closedBall 0 1) ∧
      HasDerivWithinAt (fun t => riemannianDiskArea (G t)
        ((⟨Phi t, (Phi t).contMDiff.continuous⟩ : C(M, M)).comp u))
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapMetricVariationWithinDensity H (_root_.Set.Icc a b) t₀ U z) (_root_.Set.Icc a b) t₀ := by
  let H := fun t => Diffeomorph.pullbackMetric (G t) (Phi t)
  have hquad := contMDiffOn_parameterPullbackQuadratic_of_uniqueDiffOn hG
    (uniqueDiffOn_Icc hab) hreg hPhi
  have hH₀ : H t₀ = G t₀ := by
    simp only [H, hid, Diffeomorph.pullbackMetric_refl]
  have hc : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt (H t₀) U z := by
    rwa [hH₀]
  have h := hu.hasDerivWithinAt_area_metric_on_Icc hab ht₀ hquad hc
  refine ⟨h.1, ?_⟩
  have he : (fun t => riemannianDiskArea (H t) u) =
      (fun t => riemannianDiskArea (G t)
        ((⟨Phi t, (Phi t).contMDiff.continuous⟩ : C(M, M)).comp u)) := by
    funext t
    exact hu.area_pullback (G t) (Phi t)
  rw [he] at h
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_on_Icc ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.hasDerivWithinAt_area_isotopy_on_Icc

end DifferentialGeometry.Geometry

end

end
