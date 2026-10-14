import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Topology
open _root_.Set

namespace IsCompact
open _root_.IsCompact

variable {T M : Type*} [TopologicalSpace T] [TopologicalSpace M]

open _root_.IsCompact in
theorem exists_compact_superset_of_eventually {K : Set T} (hK : IsCompact K)
    (B : T → Set M)
    (hB : ∀ t ∈ K, ∃ L : Set M, IsCompact L ∧
      ∀ᶠ s in 𝓝[K] t, B s ⊆ L) :
    ∃ L : Set M, IsCompact L ∧ ∀ t ∈ K, B t ⊆ L := by
  classical
  choose L hL hnear using hB
  obtain ⟨S, hS⟩ := hK.elim_nhdsWithin_subcover'
    (fun t ht => {s | B s ⊆ L t ht}) hnear
  refine ⟨⋃ t ∈ S, L t t.property, S.isCompact_biUnion (fun t _ => hL t t.property), ?_⟩
  intro t ht x hx
  rcases mem_iUnion₂.mp (hS ht) with ⟨s, hs, hst⟩
  exact mem_iUnion₂.mpr ⟨s, hs, hst hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_compact_superset_of_eventually then
    throwError "Refusing to shadow existing declaration IsCompact.exists_compact_superset_of_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_compact_superset_of_eventually ``Submission.IsCompact.exists_compact_superset_of_eventually

end IsCompact
