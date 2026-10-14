import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import Submission.DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_uniform_local_source_metric_bound_near_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {U K : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (η : ℝ) (C : ℝ≥0), 0 < η ∧ ∀ p ∈ K,
      _root_.Metric.closedBall p η ⊆ U ∧
      (∀ x ∈ _root_.Metric.closedBall p η, ∀ y ∈ _root_.Metric.closedBall p η,
        riemannianEDistOf g (r x) (r y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) ∧
      ∀ x ∈ _root_.Metric.closedBall p η, ∀ v : F,
        Real.sqrt (g.inner (r x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r x v)
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r x v)) ≤ C * ‖v‖ := by
  obtain ⟨η, hη, hηU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hcompact : IsCompact (_root_.Metric.cthickening η K) := hK.cthickening
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hU hr hcompact hηU
  refine ⟨η, C, hη, ?_⟩
  intro p hp
  have hball : _root_.Metric.closedBall p η ⊆ _root_.Metric.cthickening η K :=
    fun x hx => _root_.Metric.mem_cthickening_of_dist_le x p η K hp hx
  have hballU := hball.trans hηU
  refine ⟨hballU, ?_, fun x hx => hC x (hball hx)⟩
  intro x hx y hy
  exact riemannian_edist_le_on_convex_source g hU hr hballU (convex_closedBall p η)
    (fun z hz => hC z (hball hz)) hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_local_source_metric_bound_near_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_local_source_metric_bound_near_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_local_source_metric_bound_near_compact ``Submission.DifferentialGeometry.Geometry.exists_uniform_local_source_metric_bound_near_compact

end DifferentialGeometry.Geometry

end

end
