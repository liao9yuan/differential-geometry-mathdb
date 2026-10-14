import Submission.DifferentialGeometry.Topology.Circle.GermExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 1 + 1)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

omit [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
open _root_.PartialDiffeomorph in
theorem exists_disk_chart_eqOn_circle_neighborhood
    (φ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hφ : _root_.Metric.closedBall (0 : E) 1 ⊆ φ.source) (hψ : _root_.Metric.sphere (0 : E) 1 ⊆ ψ.source)
    (hboundary : φ '' _root_.Metric.sphere (0 : E) 1 = ψ '' _root_.Metric.sphere (0 : E) 1)
    (hside : _root_.Set.MapsTo ψ (_root_.Metric.closedBall (0 : E) 1 ∩ ψ.source) (φ '' _root_.Metric.closedBall (0 : E) 1)) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      _root_.Metric.closedBall (0 : E) 1 ⊆ χ.source ∧ χ '' _root_.Metric.closedBall (0 : E) 1 = φ '' _root_.Metric.closedBall (0 : E) 1 ∧
      ∃ V : Set E, IsOpen V ∧ _root_.Metric.sphere (0 : E) 1 ⊆ V ∧ V ⊆ ψ.source ∧ _root_.Set.EqOn χ ψ V := by
  let G := ψ.trans φ.symm
  have hSG : _root_.Metric.sphere (0 : E) 1 ⊆ G.source := by
    intro x hx
    refine ⟨hψ hx, ?_⟩
    have hm : ψ x ∈ φ '' _root_.Metric.sphere (0 : E) 1 := hboundary.symm ▸ _root_.Set.mem_image_of_mem ψ hx
    obtain ⟨y, hy, hyeq⟩ := hm
    change ψ x ∈ φ.target
    rw [← hyeq]
    exact φ.map_source (hφ (_root_.Metric.sphere_subset_closedBall hy))
  have hGboundary : _root_.Set.MapsTo G (_root_.Metric.sphere (0 : E) 1) (_root_.Metric.sphere (0 : E) 1) := by
    intro x hx
    have hm : ψ x ∈ φ '' _root_.Metric.sphere (0 : E) 1 := hboundary.symm ▸ _root_.Set.mem_image_of_mem ψ hx
    obtain ⟨y, hy, hyeq⟩ := hm
    change φ.symm (ψ x) ∈ _root_.Metric.sphere (0 : E) 1
    rw [← hyeq, show φ.symm (φ y) = y from φ.left_inv (hφ (_root_.Metric.sphere_subset_closedBall hy))]
    exact hy
  have hGside : _root_.Set.MapsTo G (_root_.Metric.closedBall (0 : E) 1 ∩ G.source) (_root_.Metric.closedBall (0 : E) 1) := by
    intro x hx
    obtain ⟨y, hy, hyeq⟩ := hside ⟨hx.1, hx.2.1⟩
    change φ.symm (ψ x) ∈ _root_.Metric.closedBall (0 : E) 1
    rw [← hyeq, show φ.symm (φ y) = y from φ.left_inv (hφ hy)]
    exact hy
  obtain ⟨D, hDball, V, hV, hSV, hVG, hD⟩ :=
    G.exists_diffeomorph_eqOn_circle_neighborhood hSG hGboundary hGside
  let χ := D.toPartialDiffeomorph.trans φ
  refine ⟨χ, ?_, ?_, V, hV, hSV, fun x hx => (hVG hx).1, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hφ (hDball.subset ⟨x, hx, rfl⟩)⟩
  · rw [show (χ : E → M) = φ ∘ D from rfl, _root_.Set.image_comp, hDball]
  · intro x hx
    change φ (D x) = ψ x
    rw [hD hx]
    exact φ.right_inv (hVG hx).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_disk_chart_eqOn_circle_neighborhood then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_disk_chart_eqOn_circle_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_disk_chart_eqOn_circle_neighborhood ``Submission.PartialDiffeomorph.exists_disk_chart_eqOn_circle_neighborhood

end PartialDiffeomorph
