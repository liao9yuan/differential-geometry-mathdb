import Mathlib.Topology.Maps.Proper.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Topology

namespace Topology
open _root_.Topology

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space Y] {e : T × X → Y}

open _root_.Topology in
theorem isProperMap_parametric_graph (he : Continuous e) :
    IsProperMap (fun q : T × X => (q.1, e q)) := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.prodMk he, ?_⟩
  intro 𝒰 p hp
  have ht : Filter.Tendsto (Prod.fst : T × X → T) 𝒰 (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hp
  obtain ⟨q, hqt, hq⟩ :=
    isProperMap_fst_of_compactSpace.ultrafilter_le_nhds_of_tendsto ht
  have hqe : e q = p.2 :=
    tendsto_nhds_unique ((he.tendsto q).mono_left hq)
      ((continuous_snd.tendsto p).comp hp)
  exact ⟨q, Prod.ext hqt hqe, hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.isProperMap_parametric_graph then
    throwError "Refusing to shadow existing declaration Topology.isProperMap_parametric_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.isProperMap_parametric_graph ``Submission.Topology.isProperMap_parametric_graph

open _root_.Topology in
theorem isClosedEmbedding_parametric_graph (he : Continuous e)
    (hinj : ∀ t, Function.Injective (fun x => e (t, x))) :
    IsClosedEmbedding (fun q : T × X => (q.1, e q)) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_fst.prodMk he) _ (isProperMap_parametric_graph he).isClosedMap
  rintro ⟨t, x⟩ ⟨s, y⟩ h
  have hts : t = s := congrArg Prod.fst h
  subst s
  exact Prod.ext rfl (hinj t (congrArg Prod.snd h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.isClosedEmbedding_parametric_graph then
    throwError "Refusing to shadow existing declaration Topology.isClosedEmbedding_parametric_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.isClosedEmbedding_parametric_graph ``Submission.Topology.isClosedEmbedding_parametric_graph

end Topology
