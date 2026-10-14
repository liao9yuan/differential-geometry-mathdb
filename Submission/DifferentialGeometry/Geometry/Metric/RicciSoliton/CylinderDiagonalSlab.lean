import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
open private closedSlab closedSlab_eq_image exists_normalized_slab_collar
  frontier_image_positive_tube disjoint_frontier_image_closedSlab
  from Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
open private exists_diffeomorph_orbitQuotient from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem exists_geometry_normalized_slab_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮CI, 𝓡 3⟯ M)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R) :
    let K := d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L))
    let U := d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R))
    ∃ tube : PartialDiffeomorph CI (𝓡 3) (S × ℝ) M ∞,
      (∀ p, tube p = d (Geometry.cylinderDiagonalQuotientMap
        (p.1, L + (R - L) * p.2))) ∧
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ tube.source ∧
      tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc L R)) ∧
      tube '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) = frontier K ∧
      tube '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) = frontier U ∧
      K ∪ tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = U ∧
      K ∩ tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = frontier K ∧
      frontier (tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) = frontier K ∪ frontier U ∧
      Disjoint (frontier K) (frontier U) := by
  intro K U
  obtain ⟨e, he⟩ := exists_diffeomorph_orbitQuotient
  let D := e.trans d
  have himages (A : Set (S × ℝ)) : D '' (proj '' A) =
      d '' (Geometry.cylinderDiagonalQuotientMap '' A) := by
    rw [_root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro p _
    exact congrArg d (he p)
  have hslabs (a : ℝ) : D '' closedSlab a =
      d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-a) a)) := by
    rw [closedSlab_eq_image]
    exact himages _
  obtain ⟨tube, htube, hdomain, himage, hin, hout, hunion, hinter⟩ :=
    exists_normalized_slab_collar D hL hLR
  refine ⟨tube, ?_, hdomain, himage.trans (himages _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [htube]
    exact congrArg d (he _)
  · simpa only [hslabs, K] using hin
  · simpa only [hslabs, U] using hout
  · simpa only [hslabs, K, U] using hunion
  · simpa only [hslabs, K] using hinter
  · rw [himage]
    have h := frontier_image_positive_tube D.toHomeomorph hL hLR.le
    change frontier (D '' (proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc L R))) =
      frontier (D '' closedSlab L) ∪ frontier (D '' closedSlab R) at h
    simpa only [hslabs, K, U] using h
  · have h := disjoint_frontier_image_closedSlab D.toHomeomorph hL (hL.trans hLR) hLR.ne
    change Disjoint (frontier (D '' closedSlab L)) (frontier (D '' closedSlab R)) at h
    simpa only [hslabs, K, U] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_geometry_normalized_slab_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_geometry_normalized_slab_collar target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end

section
open private closedSlab closedSlab_eq_image preimage_interior_closedSlab from Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
open private exists_diffeomorph_orbitQuotient from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

private theorem diagonalSlab_mem_interior_iff
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮((𝓡 2).prod 𝓘(ℝ, ℝ)), (𝓡 3)⟯ M) (L : ℝ) (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) :
    d (Geometry.cylinderDiagonalQuotientMap p) ∈
      interior (d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L))) ↔
        |p.2| < L := by
  obtain ⟨e,he⟩ := exists_diffeomorph_orbitQuotient
  let D := e.trans d
  have hr : D '' closedSlab L =
      d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) := by
    rw [closedSlab_eq_image, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro q hq
    change d (e (proj q)) = d (Geometry.cylinderDiagonalQuotientMap q)
    rw [he q]
  have heval : D (proj p) = d (Geometry.cylinderDiagonalQuotientMap p) := by
    change d (e (proj p)) = _
    rw [he p]
  rw [← hr, ← heval]
  change D.toHomeomorph (proj p) ∈ interior (D.toHomeomorph '' closedSlab L) ↔ _
  rw [← D.toHomeomorph.image_interior, D.toHomeomorph.injective.mem_set_image]
  change p ∈ proj ⁻¹' interior (closedSlab L) ↔ _
  rw [preimage_interior_closedSlab]
  simp only [_root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_Ioo, abs_lt]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diagonalSlab_mem_interior_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diagonalSlab_mem_interior_iff target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


private theorem diagonalSlab_subset_interior
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮((𝓡 2).prod 𝓘(ℝ, ℝ)), (𝓡 3)⟯ M)
    {L R : ℝ} (hLR : L < R) :
    d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ⊆
      interior (d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R))) := by
  rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
  apply (diagonalSlab_mem_interior_iff d R p).2
  have hab : |p.2| ≤ L := abs_le.mpr hp.2
  exact hab.trans_lt hLR

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diagonalSlab_subset_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diagonalSlab_subset_interior target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
