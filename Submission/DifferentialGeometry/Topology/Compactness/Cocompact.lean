import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.AtTopBot.Tendsto

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Filter
open scoped _root_.Topology

variable {X Y ι L : Type*} [TopologicalSpace X]

open _root_.Continuous in
theorem Continuous.comap_nhds_le_cocompact [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {q : Y} (hq : q ∉ _root_.Set.range f) :
    comap f (𝓝 q) ≤ _root_.Filter.cocompact X := by
  intro s hs
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp hs
  apply Filter.mem_comap.mpr
  refine ⟨(f '' K)ᶜ, (hK.image hf).isClosed.isOpen_compl.mem_nhds ?_, ?_⟩
  · rintro ⟨x, _, hx⟩
    exact hq ⟨x, hx⟩
  · intro x hx
    apply hKs
    intro hxK
    exact hx ⟨x, hxK, rfl⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Continuous
  let env ← Lean.getEnv
  if env.contains `Continuous.comap_nhds_le_cocompact then
    throwError "Refusing to shadow existing declaration Continuous.comap_nhds_le_cocompact"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.comap_nhds_le_cocompact ``Submission.Continuous.comap_nhds_le_cocompact

theorem tendsto_atTop_of_compact_cover [Preorder L]
    {K : ι → Set X} (hK : ∀ i, IsCompact (K i))
    {a : ι → L} (ha : _root_.Filter.Tendsto a _root_.Filter.cofinite _root_.Filter.atTop)
    {f : X → L} (hbound : ∀ᶠ i in _root_.Filter.cofinite, ∀ x ∈ K i, a i ≤ f x) :
    Tendsto f (_root_.Filter.cocompact X ⊓ 𝓟 (⋃ i, K i)) atTop := by
  apply tendsto_atTop.2
  intro b
  have hfin : {i | ¬ (b ≤ a i ∧ ∀ x ∈ K i, a i ≤ f x)}.Finite :=
    (ha.eventually_ge_atTop b).and hbound
  have hc : IsCompact (⋃ i ∈ {i | ¬ (b ≤ a i ∧ ∀ x ∈ K i, a i ≤ f x)}, K i) :=
    hfin.isCompact_biUnion (fun i _ => hK i)
  filter_upwards [Filter.mem_inf_of_left hc.compl_mem_cocompact,
    Filter.mem_inf_of_right (Filter.mem_principal_self (⋃ i, K i))] with x hx hxK
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxK
  have hbi : b ≤ a i ∧ ∀ x ∈ K i, a i ≤ f x := by
    by_contra hbi
    exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hbi, hi⟩⟩)
  exact hbi.1.trans (hbi.2 x hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `tendsto_atTop_of_compact_cover then
    throwError "Refusing to shadow existing declaration tendsto_atTop_of_compact_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `tendsto_atTop_of_compact_cover ``Submission.tendsto_atTop_of_compact_cover
