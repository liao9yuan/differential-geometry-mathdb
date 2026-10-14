/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import Submission.DifferentialGeometry.Topology.Connected.BicollarSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hBd : Disjoint J (boundaryComplex 2 K).space) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J, ∀ x ∈ K.space \ J,
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) a ∨
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) b := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd
      (U := _root_.Set.univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_bicollar hconn hJ.isConnected
    hJ.isPolyhedron.isClosed (hWK.trans _root_.Set.sdiff_subset) hW
    hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_circle

theorem IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J, ∀ x ∈ K.space \ J,
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) a ∨
      connectedComponentIn (K.space \ J) x = connectedComponentIn (K.space \ J) b := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK (U := _root_.Set.univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_bicollar hconn hJ.isConnected
    hJ.isPolyhedron.isClosed hWK hW hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_circle

open _root_.Classical in
theorem
    IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hBd : Disjoint J (boundaryComplex 2 K).space) (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J,
      let A := connectedComponentIn (K.space \ J) a
      let B := connectedComponentIn (K.space \ J) b
      Disjoint A B ∧ A ∪ B = K.space \ J ∧
        closure A ∪ closure B = K.space ∧ closure A ∩ closure B = J := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd
      (U := _root_.Set.univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_separating_bicollar
    hconn (isPolyhedron_space K).isClosed hJ.isConnected hJ.isPolyhedron.isClosed
    (hWK.trans _root_.Set.sdiff_subset) hW hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_circle

theorem IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_separating_circle
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hconn : IsPreconnected K.space) {J : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hsep : ¬ IsPreconnected (K.space \ J)) :
    ∃ a ∈ K.space \ J, ∃ b ∈ K.space \ J,
      let A := connectedComponentIn (K.space \ J) a
      let B := connectedComponentIn (K.space \ J) b
      Disjoint A B ∧ A ∪ B = K.space \ J ∧
        closure A ∪ closure B = K.space ∧ closure A ∩ closure B = J := by
  let _ : LocallyConnectedSpace K.space := locallyConnectedSpace_space K
  obtain ⟨W, ρ, _, hWK, _, hW, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK (U := _root_.Set.univ) Filter.univ_mem
  exact Topology.exists_connectedComponentIn_pair_sdiff_of_separating_bicollar
    hconn (isPolyhedron_space K).isClosed hJ.isConnected hJ.isPolyhedron.isClosed
    hWK hW hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_separating_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_separating_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_separating_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_connectedComponentIn_pair_sdiff_of_separating_circle

end DifferentialGeometry.Topology.PiecewiseLinear
