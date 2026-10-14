import Submission.DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import Submission.DifferentialGeometry.Topology.Connected.FiniteEDistance
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.Filter _root_.Metric
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem exists_local_source_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U) {x : V} (hx : x ∈ U) :
    ∃ (C : ℝ≥0) (S : Set V), S ∈ 𝓝 x ∧ ∀ y ∈ S, ∀ z ∈ S,
      riemannianEDistOf g (f y) (f z) ≤ (C : ℝ≥0∞) * _root_.EDist.edist y z := by
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hball : _root_.Metric.closedBall x (a / 2) ⊆ U :=
    (_root_.Metric.closedBall_subset_ball (by linarith : a / 2 < a)).trans haU
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hU hf
    (_root_.ProperSpace.isCompact_closedBall x (a / 2)) hball
  exact ⟨C, _root_.Metric.closedBall x (a / 2), _root_.Metric.closedBall_mem_nhds x (half_pos ha),
    fun y hy z hz => riemannian_edist_le_on_convex_source g hU hf hball
      (convex_closedBall x (a / 2)) hC hy hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_local_source_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_local_source_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_local_source_riemannian_lipschitz ``Submission.DifferentialGeometry.Geometry.exists_local_source_riemannian_lipschitz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_source_riemannian_lipschitz [T3Space M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ≥0, ∀ y ∈ S, ∀ z ∈ S,
      riemannianEDistOf g (f y) (f z) ≤ (C : ℝ≥0∞) * _root_.EDist.edist y z := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hlocal : LocallyLipschitzOn S f := by
    intro x hx
    obtain ⟨C, A, hA, hC⟩ := exists_local_source_riemannian_lipschitz g hU hf (hSU hx)
    exact ⟨C, A, mem_nhdsWithin_of_mem_nhds hA, hC⟩
  exact hlocal.exists_lipschitzOnWith_of_compact hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_compact_source_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_compact_source_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_compact_source_riemannian_lipschitz ``Submission.DifferentialGeometry.Geometry.exists_compact_source_riemannian_lipschitz

end DifferentialGeometry.Geometry
