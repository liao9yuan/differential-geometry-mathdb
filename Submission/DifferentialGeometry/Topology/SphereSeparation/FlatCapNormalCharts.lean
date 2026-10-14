import Submission.DifferentialGeometry.Topology.Embedding.FlatPatch
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.SphereSeparation.LocalNormalForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem embeddedSphereNormalChart_nonempty_of_flat_cap
    {e g : SphereTwo → EuclideanThree} (hg : _root_.Topology.IsEmbedding g)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    (χ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ χ.source)
    (hflat : ∀ x ∈ _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g (χ x) = Ψ (x, 0))
    (hfix : _root_.Set.EqOn g e (χ '' _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ)
    (hboundary : Ψ '' (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ⊆ _root_.Set.range e)
    {z : SphereTwo} (hz : g z ∉ _root_.Set.range e) : Nonempty (EmbeddedSphereNormalChart g z) := by
  have hzD : z ∈ χ '' _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    by_contra hn
    exact hz (hfix hn ▸ _root_.Set.mem_range_self z)
  obtain ⟨x, hx, rfl⟩ := hzD
  have hxlt : ‖x‖ < 1 := by
    by_contra hn
    have hnorm : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hx) (le_of_not_gt hn)
    apply hz
    rw [hflat x hx]
    exact hboundary ⟨(x, 0), ⟨mem_sphere_zero_iff_norm.mpr hnorm, rfl⟩, rfl⟩
  let ψ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict χ
    (_root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) _root_.Metric.isOpen_ball
  have hxψ : x ∈ ψ.source := ⟨hχ hx, mem_ball_zero_iff.mpr hxlt⟩
  have hformula : ∀ y ∈ ψ.source, g (ψ y) = Ψ (y, 0) := by
    intro y hy
    exact hflat y (_root_.Metric.ball_subset_closedBall hy.2)
  exact embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement hg
    (isImmersionAtOfComplement_of_flat_patch (by simp) ψ Ψ hformula hxψ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_flat_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_flat_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_flat_cap ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_flat_cap

end DifferentialGeometry.Topology.SphereSeparation
