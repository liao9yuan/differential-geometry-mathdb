/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacetLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TriangleEdgeLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LinkUnionSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_geometricLink_section_encard_le_two_of_triangle_facet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E]
    (R M N : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hMR : M.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ M.faces ∨ s ∈ N.faces)
    (hM : IsPLBall 2 M.space) (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    {a q : E} (ha : a ∈ T) (hq : q ∈ openSimplex (T.erase a))
    (hNspace : N.space = convexHull ℝ (T : Set E))
    (hqM : {q} ∈ (boundaryComplex 2 M).faces)
    (hfacet : convexHull ℝ ((T.erase a : Finset E) : Set E) ⊆
      (boundaryComplex 2 M).space)
    (ℓ : E →L[ℝ] ℝ)
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      _root_.Set.InjOn f (_root_.Insert.insert q R.vertices ∪ (T : Set E)) →
        ((SimplicialComplex.geometricLink R {q}).space ∩
          {x | f x = f q}).encard ≤ 2 := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hFcard : (T.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  have hret :=
    eventually_geometricLink_section_subsingleton_of_boundary_openSimplex_two
      M hM ℓ hqM hFcard hq hfacet hhalf hboundary
  have hlinkV : (SimplicialComplex.geometricLink M {q}).vertices ⊆ R.vertices := by
    intro v hv
    exact hMR (SimplicialComplex.geometricLink_le M {q} hv)
  filter_upwards [hret] with f hf
  intro hfinj
  have hfinjR : _root_.Set.InjOn f (_root_.Insert.insert q R.vertices) := hfinj.mono _root_.Set.subset_union_left
  have hfinjM : _root_.Set.InjOn f
      (_root_.Insert.insert q (SimplicialComplex.geometricLink M {q}).vertices) :=
    hfinjR.mono (_root_.Set.insert_subset_insert hlinkV)
  have hfinjT : _root_.Set.InjOn f (T : Set E) := hfinj.mono _root_.Set.subset_union_right
  have hcap := geometricLink_section_subsingleton_of_simplex_facet
    T hT hcard ha (openSimplex_subset_convexHull _ hq) N hNspace f hfinjT
  exact geometricLink_section_encard_le_two_of_faces_cover R M N hcover f
    (hf hfinjM) hcap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eventually_geometricLink_section_encard_le_two_of_triangle_facet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eventually_geometricLink_section_encard_le_two_of_triangle_facet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eventually_geometricLink_section_encard_le_two_of_triangle_facet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eventually_geometricLink_section_encard_le_two_of_triangle_facet

end DifferentialGeometry.Topology.PiecewiseLinear
