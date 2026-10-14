import Submission.DifferentialGeometry.Topology.Diffeomorph.Radial
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.ContDiff

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞}

open _root_.PartialDiffeomorph in
theorem exists_closedBall_subset_source_of_unit_closedBall
    (B : PartialDiffeomorph 𝓘(ℝ, E) J E M n)
    (hB : _root_.Metric.closedBall (0 : E) 1 ⊆ B.source) (r : ℝ) :
    ∃ B' : PartialDiffeomorph 𝓘(ℝ, E) J E M n,
      _root_.Metric.closedBall (0 : E) r ⊆ B'.source ∧
      _root_.Set.EqOn B' B (_root_.Metric.sphere (0 : E) 1) ∧
      B' '' _root_.Metric.ball (0 : E) 1 = B '' _root_.Metric.ball (0 : E) 1 ∧
      B' '' _root_.Metric.closedBall (0 : E) 1 = B '' _root_.Metric.closedBall (0 : E) 1 ∧
      B' '' _root_.Metric.sphere (0 : E) 1 = B '' _root_.Metric.sphere (0 : E) 1 := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (_root_.ProperSpace.isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open B.open_source hB
  have hsub : _root_.Metric.closedBall (0 : E) (δ + 1) ⊆ B.source := by
    rwa [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 1)] at hδsub
  obtain ⟨G, hGfix, hGb, hGc, hGs, hGsource⟩ :=
    Diffeomorph.exists_diffeomorph_image_closedBall_subset_ball (E := E) r
      (lt_add_of_pos_left 1 hδ)
  let G' : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n :=
    { G with
      contMDiff_toFun := G.contMDiff.of_le (by simp)
      contMDiff_invFun := G.symm.contMDiff.of_le (by simp) }
  let B' := G'.toPartialDiffeomorph.trans B
  refine ⟨B', ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hsub (_root_.Metric.ball_subset_closedBall (hGsource ⟨x, hx, rfl⟩))⟩
  · intro x hx
    change B (G x) = B x
    rw [hGfix hx]
    rfl
  · change (B ∘ G) '' _root_.Metric.ball (0 : E) 1 = _
    rw [Set.image_comp, hGb]
  · change (B ∘ G) '' _root_.Metric.closedBall (0 : E) 1 = _
    rw [Set.image_comp, hGc]
  · change (B ∘ G) '' _root_.Metric.sphere (0 : E) 1 = _
    rw [Set.image_comp, hGs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_closedBall_subset_source_of_unit_closedBall then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_closedBall_subset_source_of_unit_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_closedBall_subset_source_of_unit_closedBall ``Submission.PartialDiffeomorph.exists_closedBall_subset_source_of_unit_closedBall

end PartialDiffeomorph
