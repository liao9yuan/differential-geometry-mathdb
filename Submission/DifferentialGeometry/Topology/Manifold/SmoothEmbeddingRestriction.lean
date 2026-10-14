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
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [TopologicalSpace N] [ChartedSpace H' N]

theorem isSmoothEmbedding_restrictOpen (f : M → N) (hf : _root_.Manifold.IsSmoothEmbedding I J ∞ f)
    (U : _root_.TopologicalSpace.Opens M) : _root_.Manifold.IsSmoothEmbedding I J ∞ (fun x : U => f x.val) := by
  refine ⟨?_, hf.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm x.val
  let c := h.domChart.subtypeRestr (show Nonempty U from ⟨x⟩)
  have hc : c ∈ _root_.IsManifold.maximalAtlas I ∞ U := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn I I ∞ (h.domChart ∘ (Subtype.val : U → M)) c.source
      have hval : ContMDiff I I ∞ (Subtype.val : U → M) := contMDiff_subtype_val
      exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        hval.contMDiffOn
        (fun y hy => by simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, _root_.Set.mem_preimage] using hy)
    · intro z hz
      have hOld : ContMDiffAt I I ∞ h.domChart.symm z :=
        (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).contMDiffAt
          (h.domChart.open_target.mem_nhds (h.domChart.subtypeRestr_target_subset ⟨x⟩ hz))
      have hVal : ContMDiffAt I I ∞ (Subtype.val ∘ c.symm) z := by
        apply hOld.congr_of_eventuallyEq
        filter_upwards [c.open_target.mem_nhds hz] with y hy
        exact h.domChart.subtypeRestr_symm_apply ⟨x⟩ hy
      exact ((ContMDiffAt.subtypeVal_comp_iff U c.symm z).mp hVal).contMDiffWithinAt
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (hf.contMDiff.continuous.continuousAt.comp continuous_subtype_val.continuousAt)
    h.equiv c h.codChart (by simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, _root_.Set.mem_preimage]
      using h.mem_domChart_source) h.mem_codChart_source hc h.codChart_mem_maximalAtlas
  intro z hz
  have hzc : I.symm z ∈ c.target := hz.2
  have hzold : z ∈ (h.domChart.extend I).target :=
    ⟨hz.1, h.domChart.subtypeRestr_target_subset ⟨x⟩ hzc⟩
  have he := h.domChart.subtypeRestr_symm_apply (show Nonempty U from ⟨x⟩) hzc
  change J (h.codChart (f ((c.symm (I.symm z)).val))) = h.equiv (z, 0)
  change (c.symm (I.symm z)).val = h.domChart.symm (I.symm z) at he
  rw [he]
  exact h.writtenInCharts hzold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen ``Submission.DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
end DifferentialGeometry.Topology.Manifold
