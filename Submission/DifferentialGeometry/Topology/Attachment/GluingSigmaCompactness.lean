import Mathlib.Topology.Gluing
import Mathlib.Topology.Compactness.SigmaCompact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace TopCat.GlueData
open _root_.TopCat _root_.TopCat.GlueData

universe u
variable (D : TopCat.GlueData.{u})

open _root_.TopCat _root_.TopCat.GlueData in
theorem sigmaCompactSpace [Countable D.J] [∀ i, SigmaCompactSpace (D.U i)] :
    SigmaCompactSpace D.toGlueData.glued := by
  apply isSigmaCompact_univ_iff.mp
  have hcover : (⋃ i, Set.range (D.toGlueData.ι i)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective x
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self z⟩
  rw [← hcover]
  exact isSigmaCompact_iUnion _ fun i => isSigmaCompact_range (D.toGlueData.ι i).hom.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.sigmaCompactSpace then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.sigmaCompactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.sigmaCompactSpace ``Submission.TopCat.GlueData.sigmaCompactSpace

end TopCat.GlueData
