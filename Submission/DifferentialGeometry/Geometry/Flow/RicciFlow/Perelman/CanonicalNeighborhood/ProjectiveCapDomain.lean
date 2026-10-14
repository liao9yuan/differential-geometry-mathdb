import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
open private capCore_diagonalSlab from Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore
open private closedSlab closedSlab_eq_image isCompact_closedSlab isConnected_closedSlab
  closure_interior_closedSlab from Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
open private exists_boundary_chart_closedSlab_image from Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
open private exists_diffeomorph_orbitQuotient from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

universe u

private theorem exists_projective_compactDomain_diagonalSlab
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    {L : ℝ} (hL : 0 < L) :
    ∃ K : CompactDomain M,
      K.carrier = d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ∧
      Nonempty (CapCore K.carrier) := by
  obtain ⟨e,he⟩ := exists_diffeomorph_orbitQuotient
  let D := e.trans d
  have hr : D '' closedSlab L =
      d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) := by
    rw [closedSlab_eq_image, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro p hp
    change d (e (proj p)) = d (Geometry.cylinderDiagonalQuotientMap p)
    rw [he p]
  let K : CompactDomain M :=
    { carrier := D '' closedSlab L
      compact := (isCompact_closedSlab L).image D.continuous
      connected := (isConnected_closedSlab hL.le).image D D.continuous.continuousOn
      regular_closed := by
        change closure (interior (D.toHomeomorph '' closedSlab L)) = D.toHomeomorph '' closedSlab L
        rw [← D.toHomeomorph.image_interior, ← D.toHomeomorph.image_closure,
          closure_interior_closedSlab hL]
      boundary_chart := fun x hx => exists_boundary_chart_closedSlab_image D hL x hx }
  refine ⟨K, hr, ?_⟩
  change Nonempty (CapCore (D '' closedSlab L))
  rw [hr]
  exact capCore_diagonalSlab d hL

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projective_compactDomain_diagonalSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projective_compactDomain_diagonalSlab target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
open private diagonalSlab_mem_interior_iff from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_projective_compactDomain_around_diagonalPoint
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    {L : ℝ} (hL : 0 < L) (p : Cylinder) (hp : |p.2| < L) :
    ∃ K : CompactDomain M,
      K.carrier = d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ∧
      Nonempty (CapCore K.carrier) ∧
      d (Geometry.cylinderDiagonalQuotientMap p) ∈ interior K.carrier := by
  obtain ⟨K,hK,hcore⟩ := exists_projective_compactDomain_diagonalSlab d hL
  refine ⟨K,hK,hcore,?_⟩
  rw [hK]
  exact (diagonalSlab_mem_interior_iff d L p).2 hp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projective_compactDomain_around_diagonalPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projective_compactDomain_around_diagonalPoint target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
open private diagonalSlab_subset_interior from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab
open private exists_geometry_normalized_slab_collar from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

private theorem exists_projective_diagonal_slab_with_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (p : Cylinder) {L R : ℝ} (hp : |p.2| < L) (hLR : L < R) :
    let U := d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R))
    ∃ (K : CompactDomain M) (tube : PartialDiffeomorph IC I3 Cylinder M ∞),
      K.carrier = d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ∧
      Nonempty (CapCore K.carrier) ∧
      d (Geometry.cylinderDiagonalQuotientMap p) ∈ interior K.carrier ∧
      K.carrier ⊆ interior U ∧
      (∀ q, tube q = d (Geometry.cylinderDiagonalQuotientMap
        (q.1, L + (R - L) * q.2))) ∧
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ tube.source ∧
      tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc L R)) ∧
      tube '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) = frontier K.carrier ∧
      tube '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) = frontier U ∧
      K.carrier ∪ tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = U ∧
      K.carrier ∩ tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = frontier K.carrier ∧
      frontier (tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) = frontier K.carrier ∪ frontier U ∧
      Disjoint (frontier K.carrier) (frontier U) := by
  intro U
  have hL : 0 < L := lt_of_le_of_lt (abs_nonneg p.2) hp
  obtain ⟨K,hK,hcore,hpK⟩ := exists_projective_compactDomain_around_diagonalPoint d hL p hp
  obtain ⟨tube,htube,hdom,himage,hin,hout,hunion,hover,hfront,hdisj⟩ :=
    exists_geometry_normalized_slab_collar d hL hLR
  refine ⟨K,tube,hK,hcore,hpK,?_,htube,hdom,himage,?_,hout,?_,?_,?_,?_⟩
  · rw [hK]
    exact diagonalSlab_subset_interior d hLR
  · rw [hK]
    exact hin
  · rw [hK]
    exact hunion
  · rw [hK]
    exact hover
  · rw [hK]
    exact hfront
  · rw [hK]
    exact hdisj

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projective_diagonal_slab_with_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_projective_diagonal_slab_with_collar target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
