import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.MayerVietoris
import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.DirectedUnion
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CohomologyVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralCompactlySupportedCohomology_subsingleton_of_isEmpty
    [IsEmpty X] (n : ℕ) : Subsingleton (integralCompactlySupportedCohomology n X) := by
  let _ := integralSingularCohomology_subsingleton_of_isEmpty X n
  exact (integralCompactlySupportedToSingularCohomology_bijective n).injective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isEmpty ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_isEmpty

variable [T2Space X]

theorem integralCompactlySupportedCohomology_subsingleton_union
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [Subsingleton (integralCompactlySupportedCohomology n U)]
    [Subsingleton (integralCompactlySupportedCohomology n V)]
    [Subsingleton (integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V))] :
    Subsingleton (integralCompactlySupportedCohomology n ↥(U ∪ V)) := by
  apply (subsingleton_iff_forall_eq 0).mpr
  intro α
  obtain ⟨a, b, hab⟩ :=
    (integralCompactlySupportedCohomology_mayerVietoris_exact_union n U V hU hV α).mp
      (Subsingleton.elim _ _)
  rw [Subsingleton.elim a 0, Subsingleton.elim b 0, map_zero, map_zero, add_zero] at hab
  exact hab.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_union ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_union

theorem integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover
    {ι : Type v} (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = _root_.Set.univ)
    (hvan : ∀ i, Subsingleton (integralCompactlySupportedCohomology n (U i))) :
    Subsingleton (integralCompactlySupportedCohomology n X) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ : IsEmpty X := ⟨fun x => by
      have hx : x ∈ ⋃ i, U i := hcover ▸ _root_.Set.mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact isEmptyElim i⟩
    exact integralCompactlySupportedCohomology_subsingleton_of_isEmpty n
  | inr hι =>
    apply (subsingleton_iff_forall_eq 0).mpr
    intro α
    obtain ⟨i, β, rfl⟩ :=
      integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover
        n U hU hdir hcover α
    let _ := hvan i
    rw [Subsingleton.elim β 0, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover

end DifferentialGeometry.Topology

end
