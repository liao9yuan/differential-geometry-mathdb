import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Topology.Diffeomorph.Graph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Manifold
open _root_.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} {f : M → F}

open _root_.Manifold _root_.Manifold.IsImmersion in
theorem IsImmersion.prodMk_zero (hf : _root_.Manifold.IsImmersion I 𝓘(𝕜, F) n f) :
    IsImmersion I 𝓘(𝕜, F × V) n (fun x => (f x, (0 : V))) := by
  apply IsImmersionOfComplement.isImmersion (F := hf.complement × V)
  intro x
  let h := hf.isImmersionOfComplement_complement x
  let ψ := h.codChart.prod (OpenPartialHomeomorph.refl V)
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, F × V) n (F × V) := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · apply ContDiffOn.contMDiffOn
      exact (((contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).contDiffOn.comp
        contDiff_fst.contDiffOn (fun _ hy => hy.1)).prodMk contDiff_snd.contDiffOn)
    · apply ContDiffOn.contMDiffOn
      exact (((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).contDiffOn.comp
        contDiff_fst.contDiffOn (fun _ hy => hy.1)).prodMk contDiff_snd.contDiffOn)
  let A : (E × (hf.complement × V)) ≃L[𝕜] F × V :=
    (ContinuousLinearEquiv.prodAssoc 𝕜 E hf.complement V).symm.trans
      (h.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 V))
  apply IsImmersionAtOfComplement.mk_of_charts A h.domChart ψ
    h.mem_domChart_source ⟨h.mem_codChart_source, Set.mem_univ _⟩
    h.domChart_mem_maximalAtlas hψ
  · exact fun y hy => ⟨h.source_subset_preimage_source hy, Set.mem_univ _⟩
  · intro y hy
    change (h.codChart (f ((h.domChart.extend I).symm y)), (0 : V)) =
      (h.equiv (y, 0), 0)
    exact Prod.ext (h.writtenInCharts hy) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersion.prodMk_zero then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersion.prodMk_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersion.prodMk_zero ``Submission.Manifold.IsImmersion.prodMk_zero

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.prodMk_zero (hf : _root_.Manifold.IsSmoothEmbedding I 𝓘(𝕜, F) n f) :
    IsSmoothEmbedding I 𝓘(𝕜, F × V) n (fun x => (f x, (0 : V))) :=
  ⟨hf.isImmersion.prodMk_zero, (isEmbedding_prodMkLeft (0 : V)).comp hf.isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.prodMk_zero then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.prodMk_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.prodMk_zero ``Submission.Manifold.IsSmoothEmbedding.prodMk_zero

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.graph {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω} {f : M → F}
    (hf : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, F) n f) {g : F → V} (hg : ContDiff ℝ n g) :
    IsSmoothEmbedding I 𝓘(ℝ, F × V) n (fun x => (f x, g (f x))) := by
  have h := hf.prodMk_zero.diffeomorph_comp (Diffeomorph.graphShear
    (contDiff_const : ContDiff ℝ n (fun _ : F => (0 : V))) hg)
  simpa only [Function.comp_def, Diffeomorph.graphShear_apply, zero_add, sub_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.graph then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.graph ``Submission.Manifold.IsSmoothEmbedding.graph

end Manifold
