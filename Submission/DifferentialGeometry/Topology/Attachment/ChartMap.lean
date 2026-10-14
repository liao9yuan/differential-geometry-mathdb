import Mathlib.Topology.Gluing
import Mathlib.Topology.OpenPartialHomeomorph.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace TopCat.GlueData
open _root_.TopCat _root_.TopCat.GlueData

universe u

variable (D : TopCat.GlueData.{u})

open _root_.TopCat _root_.TopCat.GlueData in
def chartMap {Y : Type*} (i : D.J) [Nonempty (D.U i)] (f : D.U i → Y) :
    D.toGlueData.glued → Y :=
  f ∘ ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.chartMap then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.chartMap"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.chartMap ``Submission.TopCat.GlueData.chartMap

open _root_.TopCat _root_.TopCat.GlueData in
@[simp] theorem chartMap_apply {Y : Type*} (i : D.J) [Nonempty (D.U i)]
    (f : D.U i → Y) (x : D.U i) :
    D.chartMap i f (D.toGlueData.ι i x) = f x := by
  simp only [chartMap, Function.comp_apply]
  rw [(D.ι_isOpenEmbedding i).toOpenPartialHomeomorph_left_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.chartMap_apply then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.chartMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.chartMap_apply ``Submission.TopCat.GlueData.chartMap_apply

open _root_.TopCat _root_.TopCat.GlueData in
theorem chartMap_apply_overlap {Y : Type*} (i j : D.J)
    [Nonempty (D.U j)] (f : D.U j → Y) (x : D.V (i, j)) :
    D.chartMap j f (D.toGlueData.ι i (D.f i j x)) =
      f (D.f j i (D.t i j x)) := by
  rw [← D.glue_condition_apply i j x]
  exact D.chartMap_apply j f _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.chartMap_apply_overlap then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.chartMap_apply_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.chartMap_apply_overlap ``Submission.TopCat.GlueData.chartMap_apply_overlap

open _root_.TopCat _root_.TopCat.GlueData in
theorem continuousOn_chartMap {Y : Type*} [TopologicalSpace Y]
    (i : D.J) [Nonempty (D.U i)] (f : D.U i → Y) (hf : Continuous f) :
    ContinuousOn (D.chartMap i f) (Set.range (D.toGlueData.ι i)) := by
  apply hf.comp_continuousOn
  simpa only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using
    ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)).continuousOn_symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.continuousOn_chartMap then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.continuousOn_chartMap"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.continuousOn_chartMap ``Submission.TopCat.GlueData.continuousOn_chartMap

end TopCat.GlueData
end
