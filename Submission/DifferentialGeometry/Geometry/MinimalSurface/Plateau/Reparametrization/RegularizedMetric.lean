import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Regularization
import Submission.DifferentialGeometry.Geometry.Measure.Area.Regularization
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem SmoothDiskExtension.exists_regularized_pullback_metric_area_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ω : TopologicalSpace.Opens ℂ) (δ : ℝ)
      (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω),
      Metric.closedBall (0 : ℂ) 1 ⊆ Ω ∧ 0 < δ ∧
      (∀ (x : Ω) (v w : ℂ), h.inner x v w =
        pullbackMetricCoefficients g Q x.1 v w + δ * _root_.Inner.inner ℝ v w) ∧
      (∀ (x : Ω) (v : ℂ), δ * ‖v‖ ^ 2 ≤ h.inner x v v) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z) <
        riemannianDiskArea g q + ε := by
  obtain ⟨heq, N, hN, hDN, hQs⟩ := hQ
  let Ω : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  obtain ⟨δ, h, hδ, hinner, hbound, harea⟩ :=
    exists_regularized_pullback_disk_metric_area_lt g Ω hQs hDN hε
  have hid := riemannianDiskArea_eq_of_extension g q Q heq
  exact ⟨Ω, δ, h, hDN, hδ, hinner, hbound, by simpa only [hid] using harea⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_regularized_pullback_metric_area_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_regularized_pullback_metric_area_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_regularized_pullback_metric_area_lt ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_regularized_pullback_metric_area_lt

end DifferentialGeometry.Geometry

end

end
