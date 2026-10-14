import Submission.DifferentialGeometry.Topology.SimplicialComplex.Incidence
import Submission.DifferentialGeometry.Topology.SimplicialComplex.MaximalFace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E] (K : Geometry.SimplicialComplex 𝕜 E) (s : Finset E)


def geometricLink : Geometry.SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := link K.toPreAbstractSimplicialComplex s
  indep ht := K.indep (link_le K.toPreAbstractSimplicialComplex s ht)
  inter_subset_convexHull ht hu := K.inter_subset_convexHull
    (link_le K.toPreAbstractSimplicialComplex s ht)
    (link_le K.toPreAbstractSimplicialComplex s hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricLink then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricLink"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricLink ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricLink


@[simp]
theorem geometricLink_toPreAbstractSimplicialComplex :
    (geometricLink K s).toPreAbstractSimplicialComplex = link K.toPreAbstractSimplicialComplex s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_toPreAbstractSimplicialComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricLink_toPreAbstractSimplicialComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_toPreAbstractSimplicialComplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricLink_toPreAbstractSimplicialComplex


theorem geometricLink_le : geometricLink K s ≤ K := link_le K.toPreAbstractSimplicialComplex s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricLink_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_le ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricLink_le


instance finite_geometricLink_faces [Finite K.faces] : Finite (geometricLink K s).faces :=
  inferInstanceAs (Finite (link K.toPreAbstractSimplicialComplex s).faces)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finite_geometricLink_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finite_geometricLink_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finite_geometricLink_faces ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finite_geometricLink_faces


theorem mem_geometricLink_singleton (p : E) (t : Finset E) :
    t ∈ (geometricLink K {p}).faces ↔ t.Nonempty ∧ p ∉ t ∧ _root_.Insert.insert p t ∈ K.faces := by
  change (t.Nonempty ∧ Disjoint {p} t ∧ {p} ∪ t ∈ K.faces) ↔ _
  simp only [Finset.disjoint_singleton_left, Finset.singleton_union]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_geometricLink_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_geometricLink_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_geometricLink_singleton ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_geometricLink_singleton


theorem geometricLink_singleton_le_costar (p : E) :
    geometricLink K {p} ≤ geometricFaceCostar K {p} := by
  intro t ht
  refine ⟨geometricLink_le K {p} ht, ?_⟩
  have hp := (mem_geometricLink_singleton K p t).mp ht |>.2.1
  simpa only [Finset.singleton_subset_iff] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_le_costar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_le_costar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_le_costar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_le_costar


theorem geometricLink_singleton_space_subset_costar (p : E) :
    (geometricLink K {p}).space ⊆ (geometricFaceCostar K {p}).space := by
  intro x hx
  obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact Geometry.SimplicialComplex.mem_space_iff.mpr
    ⟨t, geometricLink_singleton_le_costar K p ht, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_space_subset_costar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_space_subset_costar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_space_subset_costar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricLink_singleton_space_subset_costar

end DifferentialGeometry.Topology.SimplicialComplex
