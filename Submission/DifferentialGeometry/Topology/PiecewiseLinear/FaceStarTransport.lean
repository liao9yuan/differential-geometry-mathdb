/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [dE : DecidableEq E] [dF : DecidableEq F]
  {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
  {φ : E → F} {ψ : F → E}

theorem IsGlueIso.image_subset_image_left_iff (h : IsGlueIso K L φ ψ)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    s.image φ ⊆ t.image φ ↔ s ⊆ t := by
  constructor
  · intro hsub
    have hback := Finset.image_mono ψ hsub
    rwa [h.image_image_left hs, h.image_image_left ht] at hback
  · intro hsub
    exact Finset.image_mono φ hsub

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_subset_image_left_iff with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_subset_image_left_iff"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_subset_image_left_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_subset_image_left_iff

theorem IsGlueIso.image_inter_left (h : IsGlueIso K L φ ψ)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    (s ∩ t).image φ = s.image φ ∩ t.image φ := by
  have hinv : _root_.Set.LeftInvOn ψ φ ((s : Set E) ∪ t) := by
    intro x hx
    rcases hx with hx | hx
    · exact h.left s hs x hx
    · exact h.left t ht x hx
  exact Finset.image_inter_of_injOn s t hinv.injOn

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_inter_left with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_inter_left"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_inter_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_inter_left

theorem IsGlueIso.card_inter_image_left (h : IsGlueIso K L φ ψ)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    (s.image φ ∩ t.image φ).card = (s ∩ t).card := by
  rw [← h.image_inter_left hs ht]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxs : x ∈ s := (Finset.mem_inter.mp hx).1
  have hys : y ∈ s := (Finset.mem_inter.mp hy).1
  rw [← h.left s hs x hxs, ← h.left s hs y hys, hxy]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_inter_image_left with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_inter_image_left"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_inter_image_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_inter_image_left

theorem IsGlueIso.image_erase_left (h : IsGlueIso K L φ ψ)
    {s : Finset E} (hs : s ∈ K.faces) {v : E} (hv : v ∈ s) :
    (s.erase v).image φ = (s.image φ).erase (φ v) := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hwv, hws⟩ := Finset.mem_erase.mp hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨w, hws, rfl⟩⟩
    intro hφ
    apply hwv
    rw [← h.left s hs w hws, ← h.left s hs v hv, hφ]
  · exact Finset.erase_image_subset_image_erase φ s v

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_erase_left with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_erase_left"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_erase_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_erase_left

theorem IsGlueIso.image_convexHull (h : IsGlueIso K L φ ψ)
    {s : Finset E} (hs : s ∈ K.faces) :
    simplicialMap K φ '' convexHull ℝ (s : Set E) =
      convexHull ℝ ((s.image φ : Finset F) : Set F) := by
  apply image_convexHull_simplicialMap K φ hs
  intro x hx y hy hxy
  rw [← h.left s hs x hx, ← h.left s hs y hy, hxy]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_convexHull with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_convexHull"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_convexHull ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.image_convexHull

open _root_.Classical in
theorem IsGlueIso.faceStarComplex (h : IsGlueIso K L φ ψ)
    {s : Finset E} (hs : s ∈ K.faces) :
    IsGlueIso (faceStarComplex K s) (faceStarComplex L (s.image φ)) φ ψ := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdF : dF = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro t ⟨ht, hts⟩
    refine ⟨h.image₁ t ht, ?_⟩
    simpa only [Finset.image_union] using h.image₁ (t ∪ s) hts
  · rintro t ⟨ht, hts⟩
    refine ⟨h.image₂ t ht, ?_⟩
    have hback := h.image₂ (t ∪ s.image φ) hts
    simpa only [Finset.image_union, h.image_image_left hs] using hback
  · intro t ht v hv
    exact h.left t ht.1 v hv
  · intro t ht v hv
    exact h.right t ht.1 v hv

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.faceStarComplex with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.faceStarComplex"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.faceStarComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.faceStarComplex

end DifferentialGeometry.Topology.PiecewiseLinear
