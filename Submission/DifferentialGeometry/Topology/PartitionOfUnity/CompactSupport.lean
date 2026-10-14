import Mathlib.Topology.PartitionOfUnity
import Mathlib.Algebra.Module.BigOperators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace PartitionOfUnity
open _root_.PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] {s : Set X}

open _root_.PartitionOfUnity in
def fintsupportOn (ρ : PartitionOfUnity ι X s) (K : Set X) (hK : IsCompact K) : Finset ι :=
  (ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hK).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.fintsupportOn ``Submission.PartitionOfUnity.fintsupportOn

open _root_.PartitionOfUnity in
@[simp]
theorem mem_fintsupportOn (ρ : PartitionOfUnity ι X s) (K : Set X) (hK : IsCompact K)
    (i : ι) : i ∈ ρ.fintsupportOn K hK ↔ (tsupport (ρ i) ∩ K).Nonempty :=
  Set.Finite.mem_toFinset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.mem_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.mem_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.mem_fintsupportOn ``Submission.PartitionOfUnity.mem_fintsupportOn

open _root_.PartitionOfUnity in
theorem fintsupport_subset_fintsupportOn (ρ : PartitionOfUnity ι X s)
    {K : Set X} (hK : IsCompact K) {x : X} (hx : x ∈ K) :
    ρ.fintsupport x ⊆ ρ.fintsupportOn K hK := by
  intro i hi
  rw [mem_fintsupportOn]
  exact ⟨x, (ρ.mem_fintsupport_iff x i).mp hi, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.fintsupport_subset_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.fintsupport_subset_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.fintsupport_subset_fintsupportOn ``Submission.PartitionOfUnity.fintsupport_subset_fintsupportOn

open _root_.PartitionOfUnity in
theorem finsupport_subset_fintsupportOn (ρ : PartitionOfUnity ι X s)
    {K : Set X} (hK : IsCompact K) {x : X} (hx : x ∈ K) :
    ρ.finsupport x ⊆ ρ.fintsupportOn K hK :=
  (ρ.finsupport_subset_fintsupport x).trans (ρ.fintsupport_subset_fintsupportOn hK hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.finsupport_subset_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.finsupport_subset_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.finsupport_subset_fintsupportOn ``Submission.PartitionOfUnity.finsupport_subset_fintsupportOn

open _root_.PartitionOfUnity in
theorem sum_fintsupportOn (ρ : PartitionOfUnity ι X s) {K : Set X} (hK : IsCompact K)
    {x : X} (hxK : x ∈ K) (hxs : x ∈ s) :
    ∑ i ∈ ρ.fintsupportOn K hK, ρ i x = 1 :=
  ρ.sum_finsupport' hxs (ρ.finsupport_subset_fintsupportOn hK hxK)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.sum_fintsupportOn then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.sum_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.sum_fintsupportOn ``Submission.PartitionOfUnity.sum_fintsupportOn

open _root_.PartitionOfUnity in
theorem sum_fintsupportOn_smul (ρ : PartitionOfUnity ι X s)
    {A : Type*} [AddCommMonoid A] [Module ℝ A]
    {K : Set X} (hK : IsCompact K) {f : X → A}
    (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s) (x : X) :
    ∑ i ∈ ρ.fintsupportOn K hK, ρ i x • f x = f x := by
  by_cases hfx : f x = 0
  · simp only [hfx, smul_zero, Finset.sum_const_zero]
  · rw [← Finset.sum_smul, ρ.sum_fintsupportOn hK (hfK hfx) (hfs hfx), one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartitionOfUnity.sum_fintsupportOn_smul then
    throwError "Refusing to shadow existing declaration PartitionOfUnity.sum_fintsupportOn_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `PartitionOfUnity.sum_fintsupportOn_smul ``Submission.PartitionOfUnity.sum_fintsupportOn_smul

end PartitionOfUnity
