import Submission.DifferentialGeometry.Topology.SphereSeparation.SourceHeightCylinder
import Submission.DifferentialGeometry.Topology.Handle.SphereDiskSides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_innermost_source_height_cylinder_with_disk_sides {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Set.Icc (a - ε) (a + ε) ⊆ W ∧
      let T : _root_.TopologicalSpace.Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree)
        (q : AddCircle (1 : ℝ) → Schoenflies.Plane) (V : _root_.TopologicalSpace.Opens SphereTwo)
        (C : (AddCircle (1 : ℝ) × T) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), 𝓡 2⟯ V),
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ q ∧
        _root_.Set.range q = _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ∧
        (∀ p, Ψ p 2 = a + p.2) ∧
        Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Icc (-ε) ε) =
          _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Icc (-ε) ε ∧
        (V : Set SphereTwo) = e ⁻¹' (Ψ '' (_root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ (T : Set ℝ))) ∧
        (∀ p, e (C p) = Ψ (q p.1, p.2.val)) ∧
        (∀ p, e (C p) 2 = a + p.2.val) ∧
        (∀ θ (t : T), t.val = 0 → (C (θ, t) : SphereTwo) = η θ) ∧
        ∃ b₀ b₁ : ClosedCell 2 → SphereTwo,
          _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₀ ∧
          _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₁ ∧
          _root_.Set.range (b₀ ∘ cellBoundaryInclusion 2) = _root_.Set.range η ∧
          _root_.Set.range (b₁ ∘ cellBoundaryInclusion 2) = _root_.Set.range η ∧
          _root_.Set.range b₀ ∪ _root_.Set.range b₁ = _root_.Set.univ ∧ _root_.Set.range b₀ ∩ _root_.Set.range b₁ = _root_.Set.range η ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            (∀ p, (C p : SphereTwo) ∈ interior (_root_.Set.range b₀) ↔ σ * p.2.val < 0) ∧
            (∀ p, (C p : SphereTwo) ∈ interior (_root_.Set.range b₁) ↔ 0 < σ * p.2.val) ∧
            (∀ p, (C p : SphereTwo) ∈ _root_.Set.range b₀ ↔ σ * p.2.val ≤ 0) ∧
            (∀ p, (C p : SphereTwo) ∈ _root_.Set.range b₁ ↔ 0 ≤ σ * p.2.val) := by
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, q, V, C, hη, hq, hqrange,
    hheight, hsphere, hV, hC, hCheight, hCzero⟩ :=
    exists_innermost_source_height_cylinder he hne hr hW haW
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, q, V, C, hη, hq, hqrange,
    hheight, hsphere, hV, hC, hCheight, hCzero, ?_⟩
  exact Handle.exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides
    hη hε V C.toHomeomorph hCzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_source_height_cylinder_with_disk_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_source_height_cylinder_with_disk_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_source_height_cylinder_with_disk_sides ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_source_height_cylinder_with_disk_sides

end DifferentialGeometry.Topology.SphereSeparation
