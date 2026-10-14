import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.SetTheory.Cardinal.Finite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*} (K : PreAbstractSimplicialComplex ι) (s : Finset ι)


def faceCostar : PreAbstractSimplicialComplex ι where
  faces := {t | t ∈ K ∧ ¬s ⊆ t}
  isRelLowerSet_faces := by
    intro t ht
    exact ⟨(K.isRelLowerSet_faces ht.1).1, fun u hut hu ↦
      ⟨(K.isRelLowerSet_faces ht.1).2 hut hu, fun hsu ↦ ht.2 (hsu.trans hut)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceCostar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceCostar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceCostar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceCostar


@[simp]
theorem mem_faceCostar (t : Finset ι) : t ∈ faceCostar K s ↔ t ∈ K ∧ ¬s ⊆ t := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_faceCostar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_faceCostar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_faceCostar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_faceCostar


theorem faceCostar_le : faceCostar K s ≤ K := fun _ h ↦ h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceCostar_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceCostar_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceCostar_le ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceCostar_le


theorem notMem_faceCostar_self : s ∉ faceCostar K s := fun h ↦ h.2 (Finset.Subset.refl _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.notMem_faceCostar_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.notMem_faceCostar_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.notMem_faceCostar_self ``Submission.DifferentialGeometry.Topology.SimplicialComplex.notMem_faceCostar_self

theorem faceCostar_faces_eq_diff_singleton (hs : s ∈ K) (hmax : IsMax (⟨s, hs⟩ : K.faces)) :
    (faceCostar K s).faces = K.faces \ {s} := by
  ext t
  constructor
  · rintro ⟨ht, hst⟩
    exact ⟨ht, fun he ↦ hst (by rw [Set.mem_singleton_iff.mp he])⟩
  · rintro ⟨ht, hts⟩
    refine ⟨ht, fun hst ↦ hts ?_⟩
    have hts' : t ⊆ s := hmax (show (⟨s, hs⟩ : K.faces) ≤ ⟨t, ht⟩ from hst)
    exact Finset.Subset.antisymm hts' hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceCostar_faces_eq_diff_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceCostar_faces_eq_diff_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceCostar_faces_eq_diff_singleton ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceCostar_faces_eq_diff_singleton


instance finite_faceCostar_faces [Finite K.faces] : Finite (faceCostar K s).faces :=
  Finite.of_injective (fun t : (faceCostar K s).faces ↦ (⟨t.val, t.prop.1⟩ : K.faces))
    (fun _ _ h ↦ Subtype.ext (congrArg (fun t : K.faces ↦ t.val) h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finite_faceCostar_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finite_faceCostar_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finite_faceCostar_faces ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finite_faceCostar_faces


theorem card_faceCostar_lt [Finite K.faces] (hs : s ∈ K) :
    Nat.card (faceCostar K s).faces < Nat.card K.faces := by
  let := Fintype.ofFinite K.faces
  let := Fintype.ofFinite (faceCostar K s).faces
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective
    (fun t : (faceCostar K s).faces ↦ (⟨t.val, t.prop.1⟩ : K.faces))
    (fun _ _ h ↦ Subtype.ext (congrArg (fun t : K.faces ↦ t.val) h))
  intro h
  obtain ⟨t, ht⟩ := h ⟨s, hs⟩
  have he : t.val = s := congrArg Subtype.val ht
  apply t.prop.2
  rw [he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_faceCostar_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_faceCostar_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_faceCostar_lt ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_faceCostar_lt

section Geometry

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  (K : Geometry.SimplicialComplex 𝕜 E) (s : Finset E)

def geometricFaceCostar : Geometry.SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := faceCostar K.toPreAbstractSimplicialComplex s
  indep ht := K.indep ht.1
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar


@[simp]
theorem geometricFaceCostar_toPreAbstractSimplicialComplex :
    (geometricFaceCostar K s).toPreAbstractSimplicialComplex =
      faceCostar K.toPreAbstractSimplicialComplex s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_toPreAbstractSimplicialComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_toPreAbstractSimplicialComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_toPreAbstractSimplicialComplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_toPreAbstractSimplicialComplex


theorem geometricFaceCostar_le : geometricFaceCostar K s ≤ K := fun _ h ↦ h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_le ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricFaceCostar_le


instance finite_geometricFaceCostar_faces [Finite K.faces] : Finite (geometricFaceCostar K s).faces :=
  finite_faceCostar_faces K.toPreAbstractSimplicialComplex s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finite_geometricFaceCostar_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finite_geometricFaceCostar_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finite_geometricFaceCostar_faces ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finite_geometricFaceCostar_faces

theorem space_geometricFaceCostar_union (hs : s ∈ K.facets) :
    K.space = (geometricFaceCostar K s).space ∪ convexHull 𝕜 (s : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    by_cases hst : s ⊆ t
    · exact Or.inr ((hs.2 ht hst) ▸ hxt)
    · exact Or.inl (Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, ⟨ht, hst⟩, hxt⟩)
  · rintro (hx | hx)
    · obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, ht.1, hxt⟩
    · exact Geometry.SimplicialComplex.convexHull_subset_space hs.1 hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.space_geometricFaceCostar_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.space_geometricFaceCostar_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.space_geometricFaceCostar_union ``Submission.DifferentialGeometry.Topology.SimplicialComplex.space_geometricFaceCostar_union

end Geometry

end DifferentialGeometry.Topology.SimplicialComplex
