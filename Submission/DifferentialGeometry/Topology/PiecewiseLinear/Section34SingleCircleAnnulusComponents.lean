import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusLocalConnectivity
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphericalCircleBicollar
import Submission.DifferentialGeometry.Topology.Connected.BicollarSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_connected_pair_cover_annulus_sdiff_circle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ J : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (hJ : IsPLSphere 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) :
    ∃ L R : Set E, IsConnected L ∧ IsConnected R ∧ L ∪ R = A \ J := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_two
  let _ := hchart
  let _ := hA.locallyConnectedSpace
  have hA' := hA.preimage_subtype hAS
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((Subtype.val : S → E) ⁻¹' A)))
  have hJO : J ⊆ O := by
    intro x hx
    have hxA : (⟨x, hAS (hJA hx)⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' A := hJA hx
    have hxint := (mem_interior_iff_notMem_frontier hxA).mpr fun hfr =>
      disjoint_left.mp hends hx (hA'.frontier_subset hfr)
    exact show (⟨x, hAS (hJA hx)⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' O from
      hOeq.symm ▸ hxint
  have hOA : O ∩ S ⊆ A := by
    rintro x ⟨hxO, hxS⟩
    have hx : (⟨x, hxS⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' O := hxO
    have hxint : (⟨x, hxS⟩ : S) ∈ interior ((Subtype.val : S → E) ⁻¹' A) :=
      hOeq ▸ hx
    exact show (⟨x, hxS⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' A from
      interior_subset hxint
  obtain ⟨W, ρ, -, -, hWO, hW, hρ, hzero⟩ :=
    hS.exists_bicollar_of_isPLSphere_one hJ (hJA.trans hAS)
      (mem_nhdsSetWithin.mpr ⟨O, hO, hJO, hOA⟩)
  have hWA : W ⊆ A := hWO
  have hW' : W ∈ 𝓝ˢ[A] J := nhdsSetWithin_mono_right hAS hW
  obtain ⟨a, ha, b, hb, hpair⟩ :=
    DifferentialGeometry.Topology.exists_connectedComponentIn_pair_sdiff_of_bicollar
      hA.isConnected.isPreconnected hJ.isConnected hJ.isPolyhedron.isClosed hWA hW'
      hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero
  refine ⟨connectedComponentIn (A \ J) a, connectedComponentIn (A \ J) b,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb, ?_⟩
  apply Subset.antisymm
    (_root_.Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
  intro x hx
  rcases hpair x hx with hxa | hxb
  · exact Or.inl (hxa ▸ mem_connectedComponentIn hx)
  · exact Or.inr (hxb ▸ mem_connectedComponentIn hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_connected_pair_cover_annulus_sdiff_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_connected_pair_cover_annulus_sdiff_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_connected_pair_cover_annulus_sdiff_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_connected_pair_cover_annulus_sdiff_circle

theorem IsPLCellOn.exists_connected_pair_cover_annulus_sdiff_circle {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) :
    ∃ L R : Set M, IsConnected L ∧ IsConnected R ∧ L ∪ R = A \ J := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ _root_.Set.image_mono hfront)
  have hJP : J ⊆ u '' P := hJA.trans hAP
  let τ := Function.invFunOn u P
  have hleft : _root_.Set.LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτc : ContinuousOn τ (u '' P) := (hu.isPLOn_inverse hleft).continuousOn
  have hτi : _root_.Set.InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hA' := hA.image_of_continuousOn_injOn (hτc.mono hAP) (hτi.mono hAP)
  have hA'S : τ '' A ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hAB hx
    rw [hleft (hfront hz)]
    exact hz
  have hJ' : IsPLSphere 1 (τ '' J) := hu.isPLSphere_invFunOn_image hJ hJP
  have hends' : Disjoint (τ '' J) ((τ '' A₀) ∪ (τ '' A₁)) := by
    rw [← _root_.Set.image_union]
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyP := hAP ((_root_.Set.union_subset hA.first_subset hA.second_subset) hy)
    exact disjoint_left.mp hends hx (hτi (hJP hx) hyP hxy.symm ▸ hy)
  obtain ⟨L, R, hL, hR, hLR⟩ :=
    hP.isPLSphere_frontier.exists_connected_pair_cover_annulus_sdiff_circle
      hA' hA'S hJ' (_root_.Set.image_mono hJA) hends'
  have hsub : L ∪ R ⊆ P := hLR ▸ sdiff_subset.trans (hA'S.trans hfront)
  refine ⟨u '' L, u '' R,
    hL.image u (hu.continuousOn.mono (subset_union_left.trans hsub)),
    hR.image u (hu.continuousOn.mono (subset_union_right.trans hsub)), ?_⟩
  rw [← _root_.Set.image_union, hLR, ← (hτi.mono hAP).image_sdiff_subset hJA, _root_.Set.image_image]
  exact (_root_.Set.image_congr fun x hx => hright (hAP hx.1)).trans (_root_.Set.image_id' (A \ J))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_connected_pair_cover_annulus_sdiff_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_connected_pair_cover_annulus_sdiff_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_connected_pair_cover_annulus_sdiff_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_connected_pair_cover_annulus_sdiff_circle

end DifferentialGeometry.Topology.PiecewiseLinear
