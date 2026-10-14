import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Recenter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure NeckRecenteringFields {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (k : ℕ) (δ : ℝ) (c : ℝ)
    (N : NormalizedNeck g δ k) (side : Bool) where
  buffer : ∀ x : neckBuffer (c * δ),
    (x.1.1, (if side then (1 : ℝ) else -1) * (1 + x.1.2)) ∈ neckBuffer δ
  neck : NormalizedNeck g (c * δ) k
  mark_eq : neck.sphereMark = N.sphereMark
  chart_eq : ∀ x : neckBuffer (c * δ),
    neck.chart x =
      N.chart ⟨(x.1.1, (if side then (1 : ℝ) else -1) * (1 + x.1.2)), buffer x⟩
  center_eq : ∃ hcenter : (N.sphereMark, (if side then (1 : ℝ) else -1)) ∈ neckBuffer δ,
    neck.center = N.chart ⟨(N.sphereMark, (if side then (1 : ℝ) else -1)), hcenter⟩
  scale_comparison : |neck.scale / N.scale - 1| ≤ c * δ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckRecenteringFields then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckRecenteringFields"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckRecenteringFields ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NeckRecenteringFields

theorem exists_neckRecenteringFields :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
        (g : SmoothRiemannianMetric ThreeModel M) (k : ℕ), 2 ≤ k →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ N : NormalizedNeck g δ k, ∀ side : Bool,
          Nonempty (NeckRecenteringFields g k δ c N side) := by
  obtain ⟨c, hc, δ₀, hδ₀, H⟩ := exists_universal_neck_recenter_constants
  refine ⟨c, hc, δ₀, hδ₀, ?_⟩
  intro M _ _ _ _ _ g k hk δ hδ hδle N side
  obtain ⟨hbuffer, N', hmark, hchart, hcenter, hscale⟩ := H M g k hk δ hδ hδle N side
  refine ⟨⟨hbuffer, N', hmark, ?_, hcenter, hscale⟩⟩
  intro x
  exact hchart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckRecenteringFields then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckRecenteringFields"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckRecenteringFields ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckRecenteringFields

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
