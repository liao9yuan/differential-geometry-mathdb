import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

structure ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop where
  isOpen : forall k : Nat, IsOpen (U k)
  mono_step : forall k : Nat, U k ⊆ U (k + 1)
  subset :
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen

namespace ExhaustsByOpen

theorem monotone {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) :
    Monotone U := by
  intro i j hij
  induction hij with
  | refl => intro x hx; exact hx
  | step hle ih =>
      exact Set.Subset.trans ih (hU.mono_step _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.monotone ``Submission.DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.monotone

theorem subset_of_le {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) {i j : Nat} (hij : i <= j) :
    U i ⊆ U j :=
  hU.monotone hij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.subset_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.subset_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.subset_of_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.subset_of_le

theorem comp_subseq {M : Type*} [TopologicalSpace M]
    {U : Nat -> Set M} (hU : ExhaustsByOpen U)
    {φ : Nat -> Nat} (hφ : StrictMono φ) :
    ExhaustsByOpen (fun k => U (φ k)) := by
  refine ⟨fun k => hU.isOpen (φ k),
    fun k => hU.subset_of_le (hφ.monotone (Nat.le_succ k)), ?_⟩
  intro K hK
  obtain ⟨k0, hk0⟩ := hU.subset K hK
  exact ⟨k0, fun k hk => hk0 (φ k) (le_trans hk (hφ.id_le k))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.comp_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.comp_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.comp_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.comp_subseq

end ExhaustsByOpen

end CheegerGromovCompactness
end DifferentialGeometry
