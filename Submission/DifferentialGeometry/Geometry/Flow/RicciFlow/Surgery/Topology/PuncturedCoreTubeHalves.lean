import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreDeformationRetract

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem range_tube_eq_positiveTube_union_middleSphere_union_negativeTube (a : T.Index) :
    range (T.tube a) = T.positiveTube a ∪ (T.middleSphere a ∪ T.negativeTube a) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rcases lt_trichotomy z.2.1 0 with h | h | h
    · exact Or.inr (Or.inr ⟨z, h, rfl⟩)
    · exact Or.inr (Or.inl ⟨z, h, rfl⟩)
    · exact Or.inl ⟨z, h, rfl⟩
  · rintro (h | h | h)
    · exact _root_.Set.image_subset_range _ _ h
    · exact _root_.Set.image_subset_range _ _ h
    · exact _root_.Set.image_subset_range _ _ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_eq_positiveTube_union_middleSphere_union_negativeTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_eq_positiveTube_union_middleSphere_union_negativeTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_eq_positiveTube_union_middleSphere_union_negativeTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_eq_positiveTube_union_middleSphere_union_negativeTube

theorem mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero {a : T.Index} {x : M}
    (ha : x ∈ _root_.Set.range (T.tube a)) (hz : (T.tubeCoord a x ha).2.1 ≠ 0) :
    x ∈ T.puncturedCore := by
  rw [T.mem_puncturedCore_iff]
  intro b hb
  obtain ⟨w, hw, hwz⟩ := hb
  by_cases hba : b = a
  · subst hba
    have hcoord : T.tubeCoord b x ha = w := T.tubeCoord_eq_of_eq_tube ha hwz
    rw [hcoord] at hz
    exact hz hw
  · exact Set.disjoint_left.mp (T.disjoint (Ne.symm hba)) ha ⟨w, hwz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero

theorem positiveTube_subset_puncturedCore (a : T.Index) :
    T.positiveTube a ⊆ T.puncturedCore := by
  rintro x ⟨z, hz, rfl⟩
  refine T.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero (_root_.Set.mem_range_self z) ?_
  rw [T.tubeCoord_tube]
  exact ne_of_gt hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.positiveTube_subset_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.positiveTube_subset_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.positiveTube_subset_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.positiveTube_subset_puncturedCore

theorem negativeTube_subset_puncturedCore (a : T.Index) :
    T.negativeTube a ⊆ T.puncturedCore := by
  rintro x ⟨z, hz, rfl⟩
  refine T.mem_puncturedCore_of_mem_range_of_tubeCoord_ne_zero (_root_.Set.mem_range_self z) ?_
  rw [T.tubeCoord_tube]
  exact ne_of_lt hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.negativeTube_subset_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.negativeTube_subset_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.negativeTube_subset_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.negativeTube_subset_puncturedCore

theorem union_puncturedCore_tubeHalves_eq_puncturedCore (a : T.Index) :
    T.puncturedCore ∪ (T.positiveTube a ∪ T.negativeTube a) = T.puncturedCore :=
  Set.union_eq_left.mpr
    (Set.union_subset (T.positiveTube_subset_puncturedCore a)
      (T.negativeTube_subset_puncturedCore a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.union_puncturedCore_tubeHalves_eq_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.union_puncturedCore_tubeHalves_eq_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.union_puncturedCore_tubeHalves_eq_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.union_puncturedCore_tubeHalves_eq_puncturedCore

theorem disjoint_middleSphere_tubeHalves (a : T.Index) :
    Disjoint (T.middleSphere a) (T.positiveTube a ∪ T.negativeTube a) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, rfl⟩ (h | h)
  · obtain ⟨w, hw, hwz⟩ := h
    simp only [Set.mem_ofPred_eq] at hz hw
    have hwz' : w = z := (T.embedding a).injective hwz
    subst hwz'
    exact absurd hw (not_lt_of_ge (le_of_eq hz))
  · obtain ⟨w, hw, hwz⟩ := h
    simp only [Set.mem_ofPred_eq] at hz hw
    have hwz' : w = z := (T.embedding a).injective hwz
    subst hwz'
    exact absurd hw (not_lt_of_ge (by rw [hz]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.disjoint_middleSphere_tubeHalves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.disjoint_middleSphere_tubeHalves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.disjoint_middleSphere_tubeHalves ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.disjoint_middleSphere_tubeHalves

theorem puncturedCore_ne_univ (a : T.Index) (y : Sphere 2) :
    T.puncturedCore ≠ univ := by
  intro h
  have hmem : T.tube a (y, (⟨0, by norm_num, by norm_num⟩ : _root_.Set.Icc (-2 : ℝ) 2)) ∈
      T.middleSphere a :=
    ⟨_, rfl, rfl⟩
  have hcore : T.tube a (y, (⟨0, by norm_num, by norm_num⟩ : _root_.Set.Icc (-2 : ℝ) 2)) ∈
      T.puncturedCore := by
    rw [h]
    trivial
  exact ((T.mem_puncturedCore_iff _).mp hcore a) hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_ne_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_ne_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_ne_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_ne_univ

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
