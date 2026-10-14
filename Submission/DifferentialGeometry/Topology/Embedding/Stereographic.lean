import Submission.DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.StereographicChart
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Manifold
open _root_.Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ V H}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.stereographic_comp {f : M → Metric.sphere (0 : E) 1}
    (hf : _root_.Manifold.IsSmoothEmbedding I (𝓡 n) ∞ f)
    (p : Metric.sphere (0 : E) 1) (hp : p ∉ _root_.Set.range f) :
    IsSmoothEmbedding I (𝓡 n) ∞ ((stereographic' n p) ∘ f) := by
  have hs : ∀ x, f x ∈ (stereographic' n p).source := by
    intro x
    simp only [stereographic'_source, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff]
    exact fun h => hp ⟨x, h⟩
  refine ⟨hf.isImmersion.isLocalDiffeomorphOn_comp ?_, ?_⟩
  · intro x
    exact DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn p
      ⟨x.val, by obtain ⟨y, hy⟩ := x.property; rw [← hy]; exact hs y⟩
  · let g : M → (stereographic' n p).source := fun x => ⟨f x, hs x⟩
    have hg : Topology.IsEmbedding g := hf.isEmbedding.codRestrict _ hs
    have hcomp := (stereographic' n p).isEmbedding_restrict.comp hg
    exact hcomp

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Manifold.IsSmoothEmbedding
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.stereographic_comp then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.stereographic_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.stereographic_comp ``Submission.Manifold.IsSmoothEmbedding.stereographic_comp

end Manifold
