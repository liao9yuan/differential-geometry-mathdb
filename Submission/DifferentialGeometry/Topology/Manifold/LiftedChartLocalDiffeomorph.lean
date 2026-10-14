import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.IsManifold
open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H S T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [Nonempty H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
variable [TopologicalSpace T] [ChartedSpace H T]

theorem isLocalDiffeomorph_of_lifted_charts (F : S → T)
    (hF : _root_.Topology.IsOpenEmbedding F)
    (hcharts : ∀ x : S, (chartAt H x).lift_openEmbedding hF ∈ _root_.IsManifold.maximalAtlas I ∞ T) :
    IsLocalDiffeomorph I I ∞ F := by
  intro x
  let c := chartAt H x
  let d := c.lift_openEmbedding hF
  let e := c.trans d.symm
  have hc : ContMDiffOn I I ∞ c c.source := contMDiffOn_chart
  have hc' : ContMDiffOn I I ∞ c.symm c.target := contMDiffOn_chart_symm
  have hd : ContMDiffOn I I ∞ d d.source := contMDiffOn_of_mem_maximalAtlas (hcharts x)
  have hd' : ContMDiffOn I I ∞ d.symm d.target := contMDiffOn_symm_of_mem_maximalAtlas (hcharts x)
  let D : PartialDiffeomorph I I S T ∞ :=
    { e with
      contMDiffOn_toFun := hd'.comp' hc
      contMDiffOn_invFun := hc'.comp' hd }
  refine ⟨D, ⟨mem_chart_source H x, ?_⟩, ?_⟩
  · exact c.map_source (mem_chart_source H x)
  · intro y hy
    change F y = F (c.symm (c y))
    rw [c.left_inv hy.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_lifted_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_lifted_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_lifted_charts ``Submission.DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_lifted_charts
end DifferentialGeometry.Topology.Manifold
