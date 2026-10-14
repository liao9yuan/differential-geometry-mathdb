/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SlabFaceTransport
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem inter_slab_eq_closedStar_inter_of_fiber_subset
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {p : E} (hp : {p} ∈ K.faces) (hstar : closedStar K p ⊆ A.space)
    (ℓ : E →ₗ[ℝ] ℝ) {a b : ℝ} (hpheight : ℓ p ∈ _root_.Set.Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    (hfiber : A.space ∩ {x | ℓ x = ℓ p} ⊆ closedStar K p) :
    A.space ∩ ℓ ⁻¹' _root_.Set.Icc a b = closedStar K p ∩ ℓ ⁻¹' _root_.Set.Icc a b := by
  classical
  apply Subset.antisymm _ (_root_.Set.inter_subset_inter_left _ hstar)
  rintro x ⟨hxA, hxab⟩
  refine ⟨?_, hxab⟩
  obtain ⟨T, hT, hxT⟩ := A.mem_space_iff.mp hxA
  by_cases hpT : p ∈ T
  · exact mem_iUnion₂.mpr ⟨T, ⟨hAK hT, subset_convexHull ℝ _ hpT⟩, hxT⟩
  have hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v := fun v hv =>
    hgap v (K.down_closed (hAK hT) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty
        v))
      (fun h => hpT (h ▸ hv))
  obtain ⟨f, hf, hcontrol⟩ := exists_isPLHomeomorphOn_face_slab_prism K (hAK hT) ℓ hpheight
      hvertices
  have hfx := hf.bijOn.mapsTo ⟨hxT, hxab⟩
  have hqstar := hfiber ⟨A.convexHull_subset_space hT hfx.1.1, hfx.1.2⟩
  have hiff := (hcontrol x ⟨hxT, hxab⟩).1 (starComplex K p) (starComplex_faces_subset K p)
  rw [starComplex_space K p hp] at hiff
  exact hiff.mp hqstar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_slab_eq_closedStar_inter_of_fiber_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_slab_eq_closedStar_inter_of_fiber_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_slab_eq_closedStar_inter_of_fiber_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_slab_eq_closedStar_inter_of_fiber_subset

end DifferentialGeometry.Topology.PiecewiseLinear
