/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryEuler
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BettiPolyhedra
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryHomology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodHomology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open _root_.Classical in
theorem IsOrientable.derivedNeighborhood {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (h : IsOrientable (n + 1) K) :
    IsOrientable (n + 1) (derivedNeighborhood K L) := by
  have hK'' := hK.secondDerived
  have hN := hK.derivedNeighborhood L
  exact IsOrientable.of_le (secondDerived K)
    (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L)
    (derivedNeighborhood_faces_subset K L) hK'' hN
    (h.barycentricSubdivision hK |>.barycentricSubdivision hK.barycentricSubdivision)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.derivedNeighborhood

open _root_.Classical in
theorem eulerChar_boundary_derivedNeighborhood_eq_two_mul [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces) :
    eulerChar (boundaryComplex 3 (derivedNeighborhood K L)) = 2 * eulerChar L := by
  rw [eulerChar_boundaryComplex_eq_two_mul (derivedNeighborhood K L) (hK.derivedNeighborhood L),
    eulerChar_derivedNeighborhood_eq hL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundary_derivedNeighborhood_eq_two_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundary_derivedNeighborhood_eq_two_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundary_derivedNeighborhood_eq_two_mul ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_boundary_derivedNeighborhood_eq_two_mul

open _root_.Classical in
theorem bettiOne_derivedNeighborhood_graph
    [Finite L.faces]
    (hL : L.faces ⊆ K.faces) (hd : ∀ s ∈ L.faces, s.card ≤ 2)
    (hconn : IsConnected L.space) :
    (Homology.bettiOne (derivedNeighborhood K L).space : ℤ) = 1 - eulerChar L := by
  rw [bettiOne_derivedNeighborhood_eq hL]
  exact bettiOne_graph L hd hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_graph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_graph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_derivedNeighborhood_graph

open _root_.Classical in
theorem bettiNumber_one_pos_of_boundary_component_not_sphere
    (k : Type) [Field k]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hor : IsOrientable 3 K) (hconn : IsConnected K.space)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hnot : ¬ IsPLSphere 2
      (connectedComponentComplex (boundaryComplex 3 K) c).space) :
    0 < Homology.bettiNumber k (TopCat.of K.space) 1 := by
  obtain ⟨o⟩ := hor
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite (ConnectedComponents B.space) := finite_connectedComponents_space B
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  have hstrict := faceEulerChar_lt_two_mul_card_of_component_not_sphere
    B hB c hnot
  change eulerChar B < (2 : ℤ) * Nat.card (ConnectedComponents B.space) at hstrict
  have hrank := card_otherBoundaryComponent_le_bettiNumber_two (k := k) K hK hconn o c
  change Nat.card (OtherBoundaryComponent B c) ≤
    Homology.bettiNumber k (TopCat.of K.space) 2 at hrank
  let cover : Option (OtherBoundaryComponent B c) → ConnectedComponents B.space
    | none => c
    | some d => d.1
  have hcover : Function.Surjective cover := by
    intro d
    by_cases hdc : d = c
    · subst d
      exact ⟨none, rfl⟩
    · exact ⟨some ⟨d, hdc⟩, rfl⟩
  have hcardCover := Nat.card_le_card_of_surjective cover hcover
  rw [Finite.card_option] at hcardCover
  have hcomponents : Nat.card (ConnectedComponents B.space) ≤
      Homology.bettiNumber k (TopCat.of K.space) 2 + 1 := by
    omega
  have hcomponentsInt : (Nat.card (ConnectedComponents B.space) : ℤ) ≤
      (Homology.bettiNumber k (TopCat.of K.space) 2 : ℤ) + 1 := by
    exact_mod_cast hcomponents
  have hEuler :=
    eulerChar_eq_one_sub_bettiNumber_one_add_bettiNumber_two_of_coherentOrientation
      (k := k) K hK hconn o c
  have hboundary : eulerChar B = 2 * eulerChar K := by
    simpa only [B] using eulerChar_boundaryComplex_eq_two_mul K hK
  by_contra hpos
  have hb₁ : Homology.bettiNumber k (TopCat.of K.space) 1 = 0 :=
    Nat.eq_zero_of_not_pos hpos
  rw [hb₁, Nat.cast_zero, sub_zero] at hEuler
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_one_pos_of_boundary_component_not_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_one_pos_of_boundary_component_not_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_one_pos_of_boundary_component_not_sphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiNumber_one_pos_of_boundary_component_not_sphere

open _root_.Classical in
theorem bettiOne_pos_of_boundary_component_not_sphere
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hor : IsOrientable 3 K) (hconn : IsConnected K.space)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hnot : ¬ IsPLSphere 2
      (connectedComponentComplex (boundaryComplex 3 K) c).space) :
    0 < Homology.bettiOne K.space := by
  simpa only [Homology.bettiOne] using
    bettiNumber_one_pos_of_boundary_component_not_sphere ℚ K hK hor hconn c hnot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_pos_of_boundary_component_not_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_pos_of_boundary_component_not_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_pos_of_boundary_component_not_sphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bettiOne_pos_of_boundary_component_not_sphere

end DifferentialGeometry.Topology.PiecewiseLinear
