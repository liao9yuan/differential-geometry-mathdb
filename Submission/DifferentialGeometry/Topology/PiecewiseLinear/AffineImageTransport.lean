/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [DecidableEq E] [DecidableEq F]

theorem exists_isGlueIso_of_affineOn_faces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {f : E → F}
    (hAff : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, _root_.Set.EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : _root_.Set.InjOn f K.space) :
    ∃ (L : Geometry.SimplicialComplex ℝ F) (ψ : F → E), L.faces.Finite ∧
      L.space = f '' K.space ∧ IsGlueIso K L f ψ ∧ IsPLHomeomorphOn f K.space L.space ∧
      _root_.Set.EqOn (simplicialMap K f) f K.space ∧
      (∀ t : Finset F, t ∈ L.faces ↔ ∃ s ∈ K.faces, t = s.image f) := by
  classical
  obtain ⟨L, hfin, hspace, hfaces, hpl⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces K hAff hinj
  let ψ := Function.invFunOn f K.vertices
  have hvertices : K.vertices ⊆ K.space := fun v hv =>
    K.convexHull_subset_space hv (subset_convexHull ℝ _ (Finset.mem_singleton_self v))
  have hback (s : Finset E) (hs : s ∈ K.faces) (v : E) (hv : v ∈ s) : ψ (f v) = v :=
    (hinj.mono hvertices).leftInvOn_invFunOn
      (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  refine ⟨L, ψ, hfin, hspace, ?_, hpl, simplicialMap_eq_of_forall_affineOn K f hAff, hfaces⟩
  refine ⟨fun s hs => (hfaces _).mpr ⟨s, hs, rfl⟩, ?_, hback, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (hfaces _).mp ht
    have heq : (s.image f).image ψ = s := by
      rw [Finset.image_image]
      calc
        s.image (ψ ∘ f) = s.image id := Finset.image_congr fun v hv => hback s hs v hv
        _ = s := Finset.image_id
    exact heq.symm ▸ hs
  · intro t ht v hv
    obtain ⟨s, hs, rfl⟩ := (hfaces _).mp ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rw [hback s hs w hw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isGlueIso_of_affineOn_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isGlueIso_of_affineOn_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isGlueIso_of_affineOn_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isGlueIso_of_affineOn_faces

end DifferentialGeometry.Topology.PiecewiseLinear
