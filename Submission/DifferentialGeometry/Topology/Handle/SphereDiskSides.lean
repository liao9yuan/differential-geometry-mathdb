import Submission.DifferentialGeometry.Topology.Handle.SphereDisk
import Submission.DifferentialGeometry.Topology.SphereSeparation.CylinderSides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hη : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η)
    {ε : ℝ} (hε : 0 < ε) (V : _root_.TopologicalSpace.Opens SphereTwo)
    (C : (AddCircle (1 : ℝ) × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : _root_.TopologicalSpace.Opens ℝ)) ≃ₜ V)
    (hCzero : ∀ θ t, t.val = 0 → (C (θ, t) : SphereTwo) = η θ) :
    ∃ b₀ b₁ : ClosedCell 2 → SphereTwo,
      Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₀ ∧
      Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₁ ∧
      _root_.Set.range (b₀ ∘ cellBoundaryInclusion 2) = _root_.Set.range η ∧
      _root_.Set.range (b₁ ∘ cellBoundaryInclusion 2) = _root_.Set.range η ∧
      _root_.Set.range b₀ ∪ _root_.Set.range b₁ = _root_.Set.univ ∧ _root_.Set.range b₀ ∩ _root_.Set.range b₁ = _root_.Set.range η ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        (∀ p, (C p : SphereTwo) ∈ interior (_root_.Set.range b₀) ↔ σ * p.2.val < 0) ∧
        (∀ p, (C p : SphereTwo) ∈ interior (_root_.Set.range b₁) ↔ 0 < σ * p.2.val) ∧
        (∀ p, (C p : SphereTwo) ∈ _root_.Set.range b₀ ↔ σ * p.2.val ≤ 0) ∧
        (∀ p, (C p : SphereTwo) ∈ _root_.Set.range b₁ ↔ 0 ≤ σ * p.2.val) := by
  obtain ⟨b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁, hcover, hinter⟩ :=
    exists_two_smooth_disks_sphere_of_circle hη
  have hregular₀ := closure_interior_range_closedCell_sphere 1 hb₀
  have hregular₁ := closure_interior_range_closedCell_sphere 1 hb₁
  have hfrontier₀ := (frontier_range_closedCell_sphere 1 hb₀).trans hboundary₀
  have hfrontier₁ := (frontier_range_closedCell_sphere 1 hb₁).trans hboundary₁
  let _ : Nonempty (ClosedCell 2) := ⟨⟨0, by simp⟩⟩
  let d := SphereSeparation.TwoSidedSeparation.ofClosedCover hregular₀ hregular₁
    (_root_.Set.range_nonempty b₀) (_root_.Set.range_nonempty b₁) hcover hinter hfrontier₀ hfrontier₁
  let T : _root_.TopologicalSpace.Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
  let z : T := ⟨0, by constructor <;> linarith⟩
  have hzero : ∀ p, (C p : SphereTwo) ∈ _root_.Set.range η ↔ p.2.val = 0 := by
    intro p
    constructor
    · rintro ⟨θ, hθ⟩
      have hpair : C p = C (θ, z) := Subtype.ext (hθ.symm.trans (hCzero θ z rfl).symm)
      exact congrArg (fun q => q.2.val) (C.injective hpair)
    · intro hp
      exact ⟨p.1, (hCzero p.1 p.2 hp).symm⟩
  obtain ⟨σ, hσ, h₀, h₁, hc₀, hc₁⟩ := d.sides_of_cylinder hε V C hzero
  refine ⟨b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁, hcover, hinter, σ, hσ, h₀, h₁, ?_, ?_⟩
  · simpa only [d, SphereSeparation.TwoSidedSeparation.ofClosedCover, hregular₀] using hc₀
  · simpa only [d, SphereSeparation.TwoSidedSeparation.ofClosedCover, hregular₁] using hc₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides ``Submission.DifferentialGeometry.Topology.Handle.exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides

end DifferentialGeometry.Topology.Handle
