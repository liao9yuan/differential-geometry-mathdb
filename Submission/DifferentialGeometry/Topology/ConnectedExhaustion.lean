import Submission.DifferentialGeometry.Topology.Exhaustion
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.SigmaCompact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set

variable {X : Type*} [TopologicalSpace X]

theorem ExhaustsByOpen.connectedComponentIn [PreconnectedSpace X] [LocallyConnectedSpace X]
    {U : ℕ → Set X} (hU : ExhaustsByOpen U) (p : X) :
    ExhaustsByOpen (fun n => _root_.connectedComponentIn (U n) p) := by
  have hmono : Monotone (fun n => _root_.connectedComponentIn (U n) p) :=
    fun _ _ h => connectedComponentIn_mono p (hU.monotone h)
  have hcover : ∀ y : X, ∃ n, y ∈ U n := by
    intro y
    obtain ⟨n, hn⟩ := hU.subset {y} isCompact_singleton
    exact ⟨n, hn n le_rfl (_root_.Set.mem_singleton y)⟩
  let V := ⋃ n, _root_.connectedComponentIn (U n) p
  have hVopen : IsOpen V := isOpen_iUnion fun n => (hU.isOpen n).connectedComponentIn
  have hVclosed : IsClosed V := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨n, hn⟩ := hcover y
    refine ⟨_root_.connectedComponentIn (U n) y, ?_,
      (hU.isOpen n).connectedComponentIn, mem_connectedComponentIn hn⟩
    intro z hz hzV
    obtain ⟨m, hm⟩ := mem_iUnion.mp hzV
    have hz1 := connectedComponentIn_mono y (hU.monotone (le_max_left n m)) hz
    have hz2 := connectedComponentIn_mono p (hU.monotone (le_max_right n m)) hm
    have heq := (connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm
    apply hy
    apply mem_iUnion.mpr
    refine ⟨max n m, ?_⟩
    rw [← heq]
    exact mem_connectedComponentIn (hU.monotone (le_max_left n m) hn)
  have hVuniv : V = univ := by
    obtain ⟨n, hn⟩ := hcover p
    exact (show IsClopen V from ⟨hVclosed, hVopen⟩).eq_univ
      ⟨p, mem_iUnion.mpr ⟨n, mem_connectedComponentIn hn⟩⟩
  refine ⟨fun n => (hU.isOpen n).connectedComponentIn,
    fun n => hmono (Nat.le_succ n), ?_⟩
  intro K hK
  obtain ⟨n, hn⟩ := hK.elim_directed_cover
    (fun n => _root_.connectedComponentIn (U n) p)
    (fun n => (hU.isOpen n).connectedComponentIn)
    (by change K ⊆ V; rw [hVuniv]; exact _root_.Set.subset_univ K)
    hmono.directed_le
  exact ⟨n, fun m hm => hn.trans (hmono hm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.connectedComponentIn ``Submission.DifferentialGeometry.CheegerGromovCompactness.ExhaustsByOpen.connectedComponentIn

end DifferentialGeometry.CheegerGromovCompactness

namespace CompactExhaustion
open _root_.CompactExhaustion

open _root_.Set _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

variable {X : Type*} [TopologicalSpace X]

open _root_.CompactExhaustion in
theorem exists_connected_open_exhaustion [PreconnectedSpace X]
    [LocallyConnectedSpace X] [R1Space X] (K : CompactExhaustion X) (p : X) :
    ∃ U : ℕ → Set X, ExhaustsByOpen U ∧
      (∀ n, IsCompact (closure (U n))) ∧ (∀ n, IsConnected (U n)) ∧
      ∀ n, p ∈ U n := by
  obtain ⟨N, hN⟩ := K.exists_mem p
  let V := fun n => interior (K (n + N + 1))
  have hV : ExhaustsByOpen V := by
    refine ⟨fun _ => isOpen_interior, fun n => interior_mono (K.subset (by omega)), ?_⟩
    intro C hC
    obtain ⟨k, hk⟩ := K.exists_superset_of_isCompact hC
    exact ⟨k, fun n hn => hk.trans (K.subset_interior (by omega))⟩
  have hp : ∀ n, p ∈ V n := fun n => K.subset_interior (by omega) hN
  refine ⟨fun n => _root_.connectedComponentIn (V n) p, hV.connectedComponentIn p,
    fun n => ?_, fun n => isConnected_connectedComponentIn_iff.mpr (hp n),
    fun n => mem_connectedComponentIn (hp n)⟩
  exact (K.isCompact (n + N + 1)).closure_of_subset
    ((connectedComponentIn_subset (V n) p).trans interior_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CompactExhaustion.exists_connected_open_exhaustion then
    throwError "Refusing to shadow existing declaration CompactExhaustion.exists_connected_open_exhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `CompactExhaustion.exists_connected_open_exhaustion ``Submission.CompactExhaustion.exists_connected_open_exhaustion

end CompactExhaustion
