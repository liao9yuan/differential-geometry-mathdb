import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionAdaptation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodSurgery

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_adapted_polyhedral_collar_base
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Geometry.SimplicialComplex ℝ E) [Finite H.faces]
    (hH : IsCombinatorialManifoldWithBoundary 2 H) {Z P : Set E}
    (hZ : IsPolyhedron Z) (hZH : Z ⊆ H.space) (hP : P ∈ 𝓝ˢ[H.space] Z) :
    ∃ H' L : Geometry.SimplicialComplex ℝ E, IsSubdivision H' H ∧
      H'.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ H.space ∩ P ∧ (∀ x ∈ Z, L.space ∈ 𝓝[H.space] x) ∧
      ∃ d : Finset {v : E // ({v} : Finset E) ∈ H'.faces},
        L.space = section34AnnularCollarBase H' d := by
  obtain ⟨O, hO, hZO, hOP⟩ := mem_nhdsSetWithin.mp hP
  obtain ⟨δ, hδ, hthick⟩ := hZ.isCompact.exists_cthickening_subset_open hO hZO
  obtain ⟨R, hRH, hRfin, hΓspace, -, hdiam⟩ :=
    exists_isSubdivision_restrict_space_diam_lt H hZ hZH hZ hZH hδ
  let _ : Finite R.faces := hRfin.to_subtype
  let Γ := PiecewiseLinear.restrict R Z
  let _ : Finite Γ.faces := (restrict_faces_finite R Z).to_subtype
  have hΓR : Γ.faces ⊆ R.faces := restrict_faces_subset R Z
  let L := PiecewiseLinear.derivedNeighborhood R Γ
  have hLH : L.space ⊆ H.space := (derivedNeighborhood_space_subset R Γ).trans hRH.space_eq.subset
  have hLO : L.space ⊆ O := by
    have h := derivedNeighborhood_space_subset_cthickening (K := R) (L := Γ) hdiam
    rw [show Γ.space = Z from hΓspace] at h
    exact h.trans hthick
  refine ⟨PiecewiseLinear.barycentricSubdivision R, L,
    (barycentricSubdivision_isSubdivision R).trans hRH,
    Set.toFinite _, derivedNeighborhood_faces_finite R Γ,
    (hH.of_isSubdivision hRH).derivedNeighborhood Γ,
    fun x hx => ⟨hLH hx, hOP ⟨hLO hx, hLH hx⟩⟩, ?_, ?_⟩
  · intro x hx
    rw [← hRH.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin hΓR (hΓspace.symm.subset hx)
  · exact exists_selected_dual_cells_of_derived_neighborhood R Γ hΓR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_adapted_polyhedral_collar_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_adapted_polyhedral_collar_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_adapted_polyhedral_collar_base ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_adapted_polyhedral_collar_base

end DifferentialGeometry.Topology.PiecewiseLinear
