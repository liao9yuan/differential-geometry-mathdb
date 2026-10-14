import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff

namespace Manifold
open _root_.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {f : M → E'}

open _root_.Manifold _root_.Manifold.IsImmersion in
lemma IsImmersion.continuousLinearEquiv_comp
    (hf : _root_.Manifold.IsImmersion I 𝓘(𝕜, E') n f) (e : E' ≃L[𝕜] E'') :
    IsImmersion I 𝓘(𝕜, E'') n (e ∘ f) := by
  classical
  obtain ⟨F, hFadd, hFspace, hF⟩ := hf
  let _ := hFadd
  let _ := hFspace
  apply IsImmersionOfComplement.isImmersion (F := F)
  intro x
  let h := hF x
  let ψ := e.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (h.codChart.trans e.toHomeomorph.toOpenPartialHomeomorph)
  have hψsource : ψ.source = e.symm ⁻¹' h.codChart.source := by simp [ψ]
  have hψtarget : ψ.target = e.symm ⁻¹' h.codChart.target := by simp [ψ]
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E'') n E'' := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn 𝓘(𝕜, E'') 𝓘(𝕜, E'') n
        (e ∘ h.codChart ∘ e.symm) ψ.source
      apply e.contDiff.contMDiff.comp_contMDiffOn
      apply (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        e.symm.contDiff.contMDiff.contMDiffOn
      intro y hy
      exact hψsource ▸ hy
    · change ContMDiffOn 𝓘(𝕜, E'') 𝓘(𝕜, E'') n
        (e ∘ h.codChart.symm ∘ e.symm) ψ.target
      apply e.contDiff.contMDiff.comp_contMDiffOn
      apply (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        e.symm.contDiff.contMDiff.contMDiffOn
      intro y hy
      exact hψtarget ▸ hy
  apply IsImmersionAtOfComplement.mk_of_charts (h.equiv.trans e) h.domChart ψ
    h.mem_domChart_source
  · rw [hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, e.symm_apply_apply] using
      h.mem_codChart_source
  · exact h.domChart_mem_maximalAtlas
  · exact hψ
  · intro y hy
    rw [Set.mem_preimage, hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, e.symm_apply_apply] using
      h.source_subset_preimage_source hy
  · intro y hy
    change e (h.codChart (e.symm (e (f ((h.domChart.extend I).symm y))))) =
      e (h.equiv (y, 0))
    rw [e.symm_apply_apply]
    exact congrArg e (h.writtenInCharts hy)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Manifold.IsImmersion
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersion.continuousLinearEquiv_comp then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersion.continuousLinearEquiv_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersion.continuousLinearEquiv_comp ``Submission.Manifold.IsImmersion.continuousLinearEquiv_comp

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
lemma IsSmoothEmbedding.continuousLinearEquiv_comp
    (hf : _root_.Manifold.IsSmoothEmbedding I 𝓘(𝕜, E') n f) (e : E' ≃L[𝕜] E'') :
    IsSmoothEmbedding I 𝓘(𝕜, E'') n (e ∘ f) :=
  ⟨hf.isImmersion.continuousLinearEquiv_comp e,
    e.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Manifold.IsSmoothEmbedding
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.continuousLinearEquiv_comp then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.continuousLinearEquiv_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.continuousLinearEquiv_comp ``Submission.Manifold.IsSmoothEmbedding.continuousLinearEquiv_comp

end Manifold
