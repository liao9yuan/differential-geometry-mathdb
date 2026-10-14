import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.IsManifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem isSmoothEmbedding_fromOpen (U : _root_.TopologicalSpace.Opens N) (f : M → U)
    (hf : _root_.Manifold.IsSmoothEmbedding I J ∞ f) : _root_.Manifold.IsSmoothEmbedding I J ∞ (Subtype.val ∘ f) := by
  refine ⟨?_, _root_.Topology.IsEmbedding.subtypeVal.comp hf.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm x
  let : Nonempty H' := ⟨h.codChart (f x)⟩
  let hi : _root_.Topology.IsOpenEmbedding (Subtype.val : U → N) := U.isOpen.isOpenEmbedding_subtypeVal
  let c := h.codChart.lift_openEmbedding hi
  have hc : c ∈ _root_.IsManifold.maximalAtlas J ∞ N := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · rintro y ⟨u, hu, rfl⟩
      have hOld : ContMDiffAt J J ∞ h.codChart u :=
        (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).contMDiffAt
          (h.codChart.open_source.mem_nhds hu)
      have hRes : ContMDiffAt J J ∞ (fun v : U => c v.val) u := by
        apply hOld.congr_of_eventuallyEq
        filter_upwards with v
        exact h.codChart.lift_openEmbedding_apply hi
      exact (contMDiffAt_subtype_iff.mp hRes).contMDiffWithinAt
    · exact (contMDiff_subtype_val (I := J) (U := U)).comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas)
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (continuous_subtype_val.continuousAt.comp hf.contMDiff.continuous.continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ⟨f x, h.mem_codChart_source, rfl⟩
    h.domChart_mem_maximalAtlas hc
  intro z hz
  change J (c (f ((h.domChart.extend I).symm z)).val) = h.equiv (z, 0)
  dsimp only [c]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact h.writtenInCharts hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen ``Submission.DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
end DifferentialGeometry.Topology.Manifold
