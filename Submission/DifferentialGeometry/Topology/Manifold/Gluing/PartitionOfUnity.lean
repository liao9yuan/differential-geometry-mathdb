import Submission.DifferentialGeometry.Topology.Manifold.PartitionOfUnity.Concentrated
import Submission.DifferentialGeometry.Topology.Attachment.GluingSigmaCompactness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace TopCat.GlueData
open _root_.TopCat _root_.TopCat.GlueData

universe u
variable (D : TopCat.GlueData.{u})

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H D.toGlueData.glued] [IsManifold I ∞ D.toGlueData.glued]
  [T2Space D.toGlueData.glued]

open _root_.TopCat _root_.TopCat.GlueData in
theorem exists_smoothPartitionOfUnity_chartRange_eq_single_near
    [Finite D.J] [∀ i, SigmaCompactSpace (D.U i)]
    {K : Set D.toGlueData.glued} (hK : IsClosed K) (i₀ : D.J) (z₀ : D.U i₀) :
    letI := Classical.decEq D.J
    ∃ mu : SmoothPartitionOfUnity D.J I D.toGlueData.glued K,
      mu.IsSubordinate (fun i => Set.range (D.toGlueData.ι i)) ∧
      ∃ W : Set D.toGlueData.glued, IsOpen W ∧ D.toGlueData.ι i₀ z₀ ∈ W ∧
        ∀ x ∈ W, ∀ i, mu i x = if i = i₀ then 1 else 0 := by
  let : SigmaCompactSpace D.toGlueData.glued := D.sigmaCompactSpace
  exact SmoothPartitionOfUnity.exists_isSubordinate_eq_single_near hK
    (fun i => Set.range (D.toGlueData.ι i))
    (fun i => (D.ι_isOpenEmbedding i).isOpen_range)
    (fun x _ => by
      obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective x
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self z⟩)
    i₀ (Set.mem_range_self z₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.exists_smoothPartitionOfUnity_chartRange_eq_single_near then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.exists_smoothPartitionOfUnity_chartRange_eq_single_near"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.exists_smoothPartitionOfUnity_chartRange_eq_single_near ``Submission.TopCat.GlueData.exists_smoothPartitionOfUnity_chartRange_eq_single_near

end TopCat.GlueData

end

end
