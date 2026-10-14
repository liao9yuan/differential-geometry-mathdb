import Submission.DifferentialGeometry.Topology.Manifold.InteriorChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) {n : ℕ∞ω} [IsManifold I n M]

theorem contDiffAt_comp_extChartAt_symm_of_isInteriorPoint {f : M → F}
    (hf : ContMDiff I 𝓘(𝕜, F) n f) {x : M} (hx : I.IsInteriorPoint x) :
    ContDiffAt 𝕜 n (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) := by
  let c := interiorChart I n x
  have hxc : x ∈ c.source := (mem_interiorChart_source_iff I n x).mpr hx
  exact ((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
    (c.open_target.mem_nhds (c.map_source hxc))).contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint ``Submission.DifferentialGeometry.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint

end DifferentialGeometry.Manifold
