import Submission.DifferentialGeometry.Topology.SphereSeparation.Schoenflies
import Submission.DifferentialGeometry.Topology.SphereSeparation.StandardSphere
import Submission.DifferentialGeometry.Topology.SphereSeparation.Transport
import Submission.DifferentialGeometry.Topology.Manifold.BallDiffeomorphExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_diffeomorph_of_smoothSchoenflies
    (hSch : smoothSchoenfliesThree) (e : _root_.Metric.sphere (0 : EuclideanThree) 1 → EuclideanThree)
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) EuclideanThree EuclideanThree ∞,
      D '' _root_.Metric.sphere 0 1 = _root_.Set.range e := by
  obtain ⟨φ, hφ, hφS⟩ := hSch e he
  obtain ⟨D, hD⟩ := DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall
    φ zero_lt_one hφ
  exact ⟨D, ((hD.mono _root_.Metric.sphere_subset_closedBall).image_eq).trans hφS⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies

theorem exists_ball_sphereSides_of_smoothSchoenflies
    (hSch : smoothSchoenfliesThree) (e : _root_.Metric.sphere (0 : EuclideanThree) 1 → EuclideanThree)
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) EuclideanThree EuclideanThree ∞)
      (d : SphereSides (_root_.Set.range e)),
      D '' _root_.Metric.sphere 0 1 = _root_.Set.range e ∧ d.compactSide = D '' _root_.Metric.ball 0 1 ∧
      closure d.compactSide = D '' _root_.Metric.closedBall 0 1 := by
  obtain ⟨D, hDS⟩ := exists_global_diffeomorph_of_smoothSchoenflies hSch e he
  have hDB : closure (D '' _root_.Metric.ball 0 1) = D '' _root_.Metric.closedBall 0 1 := by
    change closure (D.toHomeomorph '' _root_.Metric.ball 0 1) = D.toHomeomorph '' _root_.Metric.closedBall 0 1
    rw [← D.toHomeomorph.image_closure, closure_ball 0 one_ne_zero]
  have hside : ∃ d : SphereSides (D '' _root_.Metric.sphere 0 1),
      d.compactSide = D '' _root_.Metric.ball 0 1 ∧ closure d.compactSide = D '' _root_.Metric.closedBall 0 1 :=
    ⟨standardUnitSphereSides.image D.toHomeomorph, rfl, hDB⟩
  rw [hDS] at hside
  obtain ⟨d, hd, hdc⟩ := hside
  exact ⟨D, d, hDS, hd, hdc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_ball_sphereSides_of_smoothSchoenflies then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_ball_sphereSides_of_smoothSchoenflies"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_ball_sphereSides_of_smoothSchoenflies ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_ball_sphereSides_of_smoothSchoenflies

end DifferentialGeometry.Topology.SphereSeparation
