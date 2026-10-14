import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_planar_chart_sphere
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ e : OpenPartialHomeomorph (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℂ,
      e.source = {v}ᶜ ∧ e.target = _root_.Set.univ ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm e.target := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let s := stereographic' 2 v
  let L := Complex.orthonormalBasisOneI.repr.symm
  let e := s.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hs : s ∈ IsManifold.maximalAtlas (𝓡 2) ∞
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    IsManifold.subset_maximalAtlas ⟨v, rfl⟩
  have hss : e.source = s.source := by simp [e]
  have hst : s.target = univ := stereographic'_target v
  have het : e.target = univ := by simp [e, hst]
  refine ⟨e, hss.trans (stereographic'_source v), het, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ s.source := hss ▸ hx
    exact (L.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas hs hxs)).contMDiffWithinAt
  · intro z _
    have hsz : L.symm z ∈ s.target := hst ▸ _root_.Set.mem_univ _
    exact ((contMDiffAt_symm_of_mem_maximalAtlas hs hsz).comp z
      L.symm.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_planar_chart_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_planar_chart_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_planar_chart_sphere ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_planar_chart_sphere

end DifferentialGeometry.Topology.Manifold
