import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace IsCompact
open _root_.IsCompact

open _root_.IsCompact in
theorem exists_subset_closed_interval_prod
    {X : Type*} [TopologicalSpace X] {S : Set (ℝ × X)} (hS : IsCompact S)
    {a c : ℝ} {W : Set X} (hSW : S ⊆ _root_.Set.Ioo a c ×ˢ W) :
    ∃ a' c' : ℝ, ∃ K : Set X, a < a' ∧ c' < c ∧ IsCompact K ∧ K ⊆ W ∧
      S ⊆ _root_.Set.Icc a' c' ×ˢ K := by
  obtain ⟨a', haa, ha'⟩ := hS.exists_forall_le' continuous_fst.continuousOn
    (fun z hz => (hSW hz).1.1)
  obtain ⟨c', hcc, hc'⟩ := hS.exists_forall_le' (α := ℝᵒᵈ) continuous_fst.continuousOn
    (fun z hz => (hSW hz).1.2)
  refine ⟨a', c', Prod.snd '' S, haa, hcc, hS.image continuous_snd, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (hSW hz).2
  · intro z hz
    exact ⟨⟨ha' z hz, hc' z hz⟩, _root_.Set.mem_image_of_mem _ hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_subset_closed_interval_prod then
    throwError "Refusing to shadow existing declaration IsCompact.exists_subset_closed_interval_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_subset_closed_interval_prod ``Submission.IsCompact.exists_subset_closed_interval_prod

end IsCompact
