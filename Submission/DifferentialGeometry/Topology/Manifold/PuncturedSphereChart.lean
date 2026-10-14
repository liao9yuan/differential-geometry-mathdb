import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_punctured_sphere_chart (n : ℕ)
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ e : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (EuclideanSpace ℝ (Fin n)) ∞,
      e.source = {v}ᶜ ∧ e.target = univ := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let s := stereographic' n v
  have hs : s ∈ IsManifold.maximalAtlas (𝓡 n) ∞
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    IsManifold.subset_maximalAtlas ⟨v, rfl⟩
  let e : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toPartialEquiv := s.toPartialEquiv
      open_source := s.open_source
      open_target := s.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hs
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hs }
  exact ⟨e, stereographic'_source v, stereographic'_target v⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_punctured_sphere_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_punctured_sphere_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_punctured_sphere_chart ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_punctured_sphere_chart

end DifferentialGeometry.Topology.Manifold
