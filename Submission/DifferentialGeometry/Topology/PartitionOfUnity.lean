import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Algebra.Module.BigOperators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace PartitionOfUnity
open _root_.PartitionOfUnity

open _root_.PartitionOfUnity in
theorem exists_finset_sum_smul_eq
    {A ι F : Type*} [TopologicalSpace A] [AddCommMonoid F] [Module Real F]
    {s : Set A} (rho : PartitionOfUnity ι A s) {f : A → F}
    (hc : HasCompactSupport f) (hs : Function.support f ⊆ s) :
    ∃ t : Finset ι, ∀ x, ∑ i ∈ t, rho i x • f x = f x := by
  classical
  let t := (rho.locallyFinite.closure.finite_nonempty_inter_compact hc).toFinset
  refine ⟨t, fun x => ?_⟩
  by_cases hfx : f x = 0
  · simp only [hfx, smul_zero, Finset.sum_const_zero]
  · have hxs := subset_tsupport f hfx
    have hsub : rho.finsupport x ⊆ t := by
      intro i hi
      have hix : x ∈ tsupport (rho i) := subset_tsupport _ ((rho.mem_finsupport x).mp hi)
      exact (Set.Finite.mem_toFinset _).mpr ⟨x, hix, hxs⟩
    rw [← Finset.sum_smul, rho.sum_finsupport' (hs hfx) hsub, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.exists_finset_sum_smul_eq then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.exists_finset_sum_smul_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.exists_finset_sum_smul_eq ``Submission.PartitionOfUnity.exists_finset_sum_smul_eq

end PartitionOfUnity
