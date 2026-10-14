import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.ClosedStripDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Filter _root_.Manifold
open scoped _root_.Topology _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_smooth_boundary_collar_strip
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ c : BoundaryManifold (𝓡∂ (n + 1)) M × _root_.Set.Icc (0 : ℝ) ε → M,
        Topology.IsClosedEmbedding c ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        (∀ p (t : _root_.Set.Icc (0 : ℝ) ε), 0 < (t : ℝ) → (𝓡∂ (n + 1)).IsInteriorPoint (c (p, t))) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
          IsOpen (c '' {q | (q.2 : ℝ) < δ}) ∧
          (𝓡∂ (n + 1)).boundary M ⊆ c '' {q | (q.2 : ℝ) < δ} := by
  obtain ⟨ε, hε, c, hc, hcs, hc0, hi, δ, hδ, hδε, Y, hKY, hY, _, _⟩ :=
    exists_closed_boundary_collar_diffeomorph hK
  refine ⟨ε, hε, c, hc, hcs, hc0, (fun p t ht => hi (p, t) ht),
    δ, hδ, hδε, ?_, ?_⟩
  · exact hY ▸ Y.isOpen
  · exact hY ▸ hKY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.exists_smooth_boundary_collar_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.exists_smooth_boundary_collar_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.exists_smooth_boundary_collar_strip ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_smooth_boundary_collar_strip

end DifferentialGeometry.Manifold.BoundaryCollar
