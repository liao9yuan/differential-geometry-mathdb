import Submission.DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import Submission.DifferentialGeometry.Topology.Manifold.ParametrizationDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [HasSmoothBoundary E H I] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [BoundarylessManifold J M]

theorem isPreconnected_interior_target_of_smooth_parametrization [PreconnectedSpace P]
    (e : PartialEquiv P M) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff I J ∞ e) (hei : ContMDiffOn J I ∞ e.symm e.target)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsPreconnected (interior e.target) := by
  obtain ⟨hemb, hinj⟩ :=
    DifferentialGeometry.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv e hes he hei
  have hrange : _root_.Set.range e = e.target := by
    rw [← _root_.Set.image_univ, ← hes, e.image_source_eq_target]
  rw [← hrange]
  exact isPreconnected_interior_range_of_fullRank_embedding e he hemb hinj hdim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_target_of_smooth_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_target_of_smooth_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_target_of_smooth_parametrization ``Submission.DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_target_of_smooth_parametrization

theorem closure_interior_target_of_smooth_parametrization [CompactSpace P] [T2Space M]
    (e : PartialEquiv P M) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff I J ∞ e) (hei : ContMDiffOn J I ∞ e.symm e.target)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    closure (interior e.target) = e.target := by
  obtain ⟨hemb, hinj⟩ :=
    DifferentialGeometry.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv e hes he hei
  have hrange : _root_.Set.range e = e.target := by
    rw [← _root_.Set.image_univ, ← hes, e.image_source_eq_target]
  rw [← hrange]
  exact closure_interior_range_of_fullRank_closedEmbedding e he
    (he.continuous.isClosedEmbedding hemb.injective) hinj hdim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.closure_interior_target_of_smooth_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.closure_interior_target_of_smooth_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.closure_interior_target_of_smooth_parametrization ``Submission.DifferentialGeometry.Geometry.Boundary.closure_interior_target_of_smooth_parametrization

end DifferentialGeometry.Geometry.Boundary
