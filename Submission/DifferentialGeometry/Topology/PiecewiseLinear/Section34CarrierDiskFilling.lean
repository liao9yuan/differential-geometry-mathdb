import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusCarrierRims
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedDiskFilling
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorDiskRemoval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_annular_disk_of_disk_in_solid_torus {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ D J T : Set M} (hS : IsPLCellOn 3 S B)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B) (hAT : A ⊆ T)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) (hT : IsTopologicalSolidTorus T)
    (hcarry : CarriesFundamentalGroupOnto A₀ T) (hD : IsPLCellOn 2 D J) (hDT : D ⊆ T) :
    ∃ F : Set M, IsPLCellOn 2 F J ∧ F ⊆ A := by
  rcases hS.exists_disk_in_annulus_or_separating_ends hA hAB hJ hJA hends with h | h
  · exact h
  · obtain ⟨D₀, D₁, hcover, hmeet, hD₀, -, h₀, h₁⟩ := h
    have hD₁ : Disjoint D₀ A₁ := by
      refine disjoint_left.mpr fun x hxD hx₁ => ?_
      exact disjoint_left.mp hends (hmeet.subset ⟨hxD, h₁ hx₁⟩) (Or.inr hx₁)
    have hgen := hS.carriesFundamentalGroupOnto_boundary_of_annulus_end hD₀ hA hAB
      (hcover ▸ _root_.Set.subset_union_left) hJA h₀ (hends.mono_right _root_.Set.subset_union_left).symm
      hD₁ hAT hcarry
    have hne : J.Nonempty := by
      obtain ⟨P, hP⟩ := hJ
      exact P.piece.bijOn.image_eq ▸ hP.nonempty.image P.piece.map
    exact (hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT hne
      hD.boundary_subset hgen).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_annular_disk_of_disk_in_solid_torus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_annular_disk_of_disk_in_solid_torus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_annular_disk_of_disk_in_solid_torus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_annular_disk_of_disk_in_solid_torus

theorem IsPLHomeomorphInto.exists_interior_filling_of_annular_disk {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKP : K.space ⊆ P)
    (hT : IsTopologicalSolidTorus K.space) {S B A A₀ A₁ D J : Set M}
    (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B)
    (hAT : A ⊆ interior (u '' K.space)) (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJA : J ⊆ A) (hends : Disjoint J (A₀ ∪ A₁))
    (hcarry : CarriesFundamentalGroupOnto A₀ (u '' K.space))
    (hD : IsPLCellOn 2 D J) (hDT : D ⊆ interior (u '' K.space)) (htrace : D ∩ B = J) :
    ∃ F C : Set M, IsPLCellOn 2 F J ∧ F ⊆ A ∧ IsPLCellOn 3 C (D ∪ F) ∧
      C ⊆ interior (u '' K.space) ∧ D ∩ F = J := by
  have hT' := hT.image_of_continuousOn_injOn (hu.continuousOn.mono hKP)
    (hu.injOn.mono hKP)
  obtain ⟨F, hF, hFA⟩ := hS.exists_annular_disk_of_disk_in_solid_torus hA hAB
    (hAT.trans interior_subset) hJ hJA hends hT' hcarry hD (hDT.trans interior_subset)
  have hDF : D ∩ F = J := by
    apply Subset.antisymm
    · exact fun x hx => htrace.subset ⟨hx.1, hAB (hFA hx.2)⟩
    · exact _root_.Set.subset_inter hD.boundary_subset hF.boundary_subset
  obtain ⟨C, hC, hCT⟩ := hu.exists_filling_of_disk_pair_in_torus K hK hKP hT hD hF
    (hDT.trans interior_subset) ((hFA.trans hAT).trans interior_subset) hDF
  exact ⟨F, C, hF, hFA, hC,
    hC.subset_interior_of_boundary_subset hCT (_root_.Set.union_subset hDT (hFA.trans hAT)), hDF⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_interior_filling_of_annular_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_interior_filling_of_annular_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_interior_filling_of_annular_disk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.exists_interior_filling_of_annular_disk

end DifferentialGeometry.Topology.PiecewiseLinear
