import Mathlib.Topology.PartitionOfUnity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set
open scoped _root_.Topology

namespace PartitionOfUnity
open _root_.PartitionOfUnity

variable {ι M : Type*} [TopologicalSpace M]

open _root_.PartitionOfUnity in
theorem sum_finset_le_one {s₀ : Set M} (ρ : PartitionOfUnity ι M s₀)
    (s : Finset ι) (x : M) : (∑ i ∈ s, ρ i x) ≤ 1 := by
  classical
  calc
    _ ≤ ∑ i ∈ s ∪ ρ.finsupport x, ρ i x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun i _ _ => ρ.nonneg i x)
    _ = ∑ᶠ i, ρ i x := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro i hi
      exact Finset.mem_union.mpr (Or.inr ((ρ.mem_finsupport x).mpr hi))
    _ ≤ 1 := ρ.sum_le_one x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.sum_finset_le_one then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.sum_finset_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.sum_finset_le_one ``Submission.PartitionOfUnity.sum_finset_le_one

end PartitionOfUnity

end

end
