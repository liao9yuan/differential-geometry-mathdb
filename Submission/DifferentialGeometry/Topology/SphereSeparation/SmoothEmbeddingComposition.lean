import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace Manifold
open _root_.Manifold

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type u} {N' : Type v} [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G N'] [IsManifold J n N']
  {f : M → N}

namespace IsImmersionOfComplement
open _root_.Manifold _root_.Manifold.IsImmersionOfComplement

open _root_.Manifold _root_.Manifold.IsImmersionOfComplement in
theorem postcomp_diffeomorph
    (hf : _root_.Manifold.IsImmersionOfComplement F I J n f)
    (ψ : Diffeomorph J J N N' n) :
    IsImmersionOfComplement F I J n (ψ ∘ f) := by
  intro x
  let h := hf x
  let c : OpenPartialHomeomorph N' G :=
    ψ.symm.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ IsManifold.maximalAtlas J n N' := by
    apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        ψ.symm.contMDiff.contMDiffOn (by
          intro y hy
          simpa [c] using hy.2)
    · have hsub : c.target ⊆ h.codChart.target := by
        intro y hy
        simpa [c] using hy
      have hsmooth := ψ.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas
          h.codChart_mem_maximalAtlas).mono hsub)
      simpa [c, Function.comp_def] using hsmooth
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (ψ.continuous.continuousAt.comp h.continuousAt) h.equiv
    h.domChart c h.mem_domChart_source
  · simp [c, h.mem_codChart_source]
  · exact h.domChart_mem_maximalAtlas
  · exact hc
  · intro y hy
    simpa [c, Function.comp_def] using h.writtenInCharts hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersionOfComplement.postcomp_diffeomorph then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersionOfComplement.postcomp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersionOfComplement.postcomp_diffeomorph ``Submission.Manifold.IsImmersionOfComplement.postcomp_diffeomorph

end IsImmersionOfComplement

namespace IsImmersion
open _root_.Manifold _root_.Manifold.IsImmersion

open _root_.Manifold _root_.Manifold.IsImmersion in
theorem postcomp_diffeomorph
    (hf : _root_.Manifold.IsImmersion I J n f) (ψ : Diffeomorph J J N N' n) :
    IsImmersion I J n (ψ ∘ f) := by
  rcases hf with ⟨F, hFgroup, hFspace, hf⟩
  let _ := hFgroup
  let _ := hFspace
  exact ⟨F, inferInstance, inferInstance, hf.postcomp_diffeomorph ψ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersion.postcomp_diffeomorph then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersion.postcomp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersion.postcomp_diffeomorph ``Submission.Manifold.IsImmersion.postcomp_diffeomorph

end IsImmersion

namespace IsSmoothEmbedding
open _root_.Manifold _root_.Manifold.IsSmoothEmbedding

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem postcomp_diffeomorph
    (hf : _root_.Manifold.IsSmoothEmbedding I J n f) (ψ : Diffeomorph J J N N' n) :
    IsSmoothEmbedding I J n (ψ ∘ f) :=
  ⟨hf.isImmersion.postcomp_diffeomorph ψ,
    ψ.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.postcomp_diffeomorph then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.postcomp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.postcomp_diffeomorph ``Submission.Manifold.IsSmoothEmbedding.postcomp_diffeomorph

end IsSmoothEmbedding

end Manifold
