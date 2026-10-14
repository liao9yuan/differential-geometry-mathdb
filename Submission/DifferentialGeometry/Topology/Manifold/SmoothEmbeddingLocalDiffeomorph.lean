import Submission.DifferentialGeometry.Topology.Manifold.SmoothLiftedCharts
import Mathlib.Geometry.Manifold.SmoothEmbedding

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
variable {E F G H H' H'' M N P : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [Nonempty H'']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H') (K : ModelWithCorners ℝ G H'')
variable [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
variable [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

theorem isSmoothEmbedding_openLocalDiffeomorph_comp
    (f : M → N) (hf : _root_.Manifold.IsSmoothEmbedding I J ∞ f)
    (g : N → P) (hg : _root_.Topology.IsOpenEmbedding g) (hs : IsLocalDiffeomorph J K ∞ g)
    (B : H' ≃ₘ⟮J, K⟯ H'') (A : F ≃L[ℝ] G) (hA : ∀ y, K (B y) = A (J y)) :
    IsSmoothEmbedding I K ∞ (g ∘ f) := by
  refine ⟨?_, hg.isEmbedding.comp hf.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  suffices h : _root_.Manifold.IsImmersionOfComplement C I K ∞ (g ∘ f) from h.isImmersion
  intro x
  let h := hImm x
  let e := h.codChart.transHomeomorph B.toHomeomorph
  let d := e.lift_openEmbedding hg
  have he : ContMDiffOn J K ∞ e e.source :=
    B.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas)
  have he' : ContMDiffOn K J ∞ e.symm e.target :=
    (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
      B.symm.contMDiff.contMDiffOn (fun _ hy => hy)
  have hd : d ∈ _root_.IsManifold.maximalAtlas K ∞ P :=
    d.mem_maximalAtlas_of_contMDiffOn
      (contMDiffOn_lift_openEmbedding J K K g hg hs e he)
      (contMDiffOn_lift_openEmbedding_symm J K K g hg hs.contMDiff e he')
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    ((hs.contMDiff.comp hf.contMDiff).continuous.continuousAt) (h.equiv.trans A)
    h.domChart d h.mem_domChart_source ⟨f x, h.mem_codChart_source, rfl⟩
    h.domChart_mem_maximalAtlas hd
  intro z hz
  change K (d (g (f ((h.domChart.extend I).symm z)))) = A (h.equiv (z, 0))
  dsimp only [d]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change K (B (h.codChart (f ((h.domChart.extend I).symm z)))) = A (h.equiv (z, 0))
  rw [hA]
  exact congrArg A (h.writtenInCharts hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_openLocalDiffeomorph_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_openLocalDiffeomorph_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_openLocalDiffeomorph_comp ``Submission.DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_openLocalDiffeomorph_comp
end DifferentialGeometry.Topology.Manifold
