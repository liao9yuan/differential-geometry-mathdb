import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem subset_boundaryComplex_complement_of_inter_subset_iUnion {ι : Type*} {n : ℕ}
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 2) A) (hAK : A.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary (n + 2) R)
    (hRspace : R.space = closure (K.space \ A.space))
    {D : Set E} (hD : IsPLBall (n + 1) D) (hDK : D ⊆ (boundaryComplex (n + 2) K).space)
    (d : Finset ι) (C : ι → Set E) (m : ι → ℕ)
    (hC : ∀ i ∈ d, IsPLBall (m i) (C i)) (hCD : ∀ i ∈ d, C i ⊆ D)
    (hm : ∀ i ∈ d, m i < n + 1) (hcover : D ∩ A.space ⊆ ⋃ i ∈ d, C i) :
    D ⊆ (boundaryComplex (n + 2) R).space := by
  have hdense := hD.closure_sdiff_eq_of_inter_subset_iUnion d C m hC hCD hm hcover
  have hsub := closure_mono (_root_.Set.sdiff_subset_sdiff_left (t := A.space) hDK)
  rw [hdense] at hsub
  rw [boundaryComplex_space_of_closure_sdiff K A R hK hA hAK hR hRspace]
  exact hsub.trans _root_.Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_inter_subset_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_inter_subset_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_inter_subset_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_inter_subset_iUnion

open _root_.Classical in
theorem subset_boundaryComplex_complement_of_boundary_inter_subset_iUnion {ι : Type*} {n : ℕ}
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 2) A) (hAK : A.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary (n + 2) R)
    (hRspace : R.space = closure (K.space \ A.space))
    {D : Set E} (hD : IsPLBall (n + 1) D) (hDA : D ⊆ (boundaryComplex (n + 2) A).space)
    (d : Finset ι) (C : ι → Set E) (m : ι → ℕ)
    (hC : ∀ i ∈ d, IsPLBall (m i) (C i)) (hCD : ∀ i ∈ d, C i ⊆ D)
    (hm : ∀ i ∈ d, m i < n + 1)
    (hcover : D ∩ (boundaryComplex (n + 2) K).space ⊆ ⋃ i ∈ d, C i) :
    D ⊆ (boundaryComplex (n + 2) R).space := by
  have hdense := hD.closure_sdiff_eq_of_inter_subset_iUnion d C m hC hCD hm hcover
  have hsub := closure_mono
    (_root_.Set.sdiff_subset_sdiff_left (t := (boundaryComplex (n + 2) K).space) hDA)
  rw [hdense] at hsub
  rw [boundaryComplex_space_of_closure_sdiff K A R hK hA hAK hR hRspace]
  exact hsub.trans _root_.Set.subset_union_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_boundary_inter_subset_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_boundary_inter_subset_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_boundary_inter_subset_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subset_boundaryComplex_complement_of_boundary_inter_subset_iUnion

end DifferentialGeometry.Topology.PiecewiseLinear
