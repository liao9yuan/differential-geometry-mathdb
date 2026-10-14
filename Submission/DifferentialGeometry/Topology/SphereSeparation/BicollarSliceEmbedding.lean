import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarSliceSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

theorem isSmoothEmbedding_bicollarSliceMap
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (c : AxialInterval a) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (bicollarSliceMap Φ c) := by
  let ι : SphereTwo → SphereTwo × AxialInterval a := fun z => (z, c)
  have hproj : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞ (Prod.fst ∘ ι) :=
    Manifold.IsSmoothEmbedding.id
  have hι : Manifold.IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ ι :=
    hproj.of_comp (J := (𝓡 2).prod 𝓘(ℝ, ℝ)) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  exact hΦ.comp hι (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isSmoothEmbedding_bicollarSliceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isSmoothEmbedding_bicollarSliceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isSmoothEmbedding_bicollarSliceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.isSmoothEmbedding_bicollarSliceMap

end DifferentialGeometry.Topology.SphereSeparation
