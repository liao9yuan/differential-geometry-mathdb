import Submission.DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r : ℝ} (hr : 0 < r) (hrs : _root_.Metric.closedBall (0 : E) r ⊆ φ.source) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, _root_.Set.EqOn D φ (_root_.Metric.closedBall 0 r) := by
  obtain ⟨A, ε, F, _, hε, _, hformula, _⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ hr hrs isOpen_univ (_root_.Set.subset_univ _)
  let B : E ≃L[ℝ] E := (Units.mk0 ε hε.ne') • A
  let T := DifferentialGeometry.Topology.translateDiffeomorph (φ 0)
  let D := (B.toDiffeomorph.trans T).trans F.symm
  refine ⟨D, ?_⟩
  intro x hx
  change F.symm (ε • A x + φ 0) = φ x
  rw [← hformula x hx, F.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall

end DifferentialGeometry.Topology.Manifold
