/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Vocabulary

def edgesAt (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (v : EuclideanSpace ℝ (Fin 3)) : Set (Finset (EuclideanSpace ℝ (Fin 3))) :=
  {e | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.edgesAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.edgesAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.edgesAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.edgesAt

structure IsPolyhedralTubeNeighborhood
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) : Prop where
  facesFinite : XK.faces.Finite
  isManifold : IsCombinatorialManifoldWithBoundary 3 XK
  isNeighborhood : XK.space ∈ nhdsSet (h '' K.space)
  subsetInterior : XK.space ⊆ interior N'
  rimDisjoint : ∀ e ∈ K.faces, e.card = 2 → Disjoint (Ebd e) XK.space
  crossing : ∀ e ∈ K.faces, e.card = 2 → ∀ x ∈ Ec e ∩ frontier XK.space,
    HasPLCrossingAt (Eint e) (frontier XK.space) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralTubeNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralTubeNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralTubeNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralTubeNeighborhood

def HasSinglePolygonTraces (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (Ec : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ e ∈ K.faces, e.card = 2 →
    IsPLSphere 1 (Ec e ∩ frontier X) ∧
    ∃ DJint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (Ec e ∩ X) DJint ∧
      (Ec e ∩ X) \ DJint = Ec e ∩ frontier X ∧ h (e.centroid ℝ id) ∈ DJint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasSinglePolygonTraces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasSinglePolygonTraces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasSinglePolygonTraces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasSinglePolygonTraces

open _root_.Classical in
def HasConnectedHandlePieces (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (Ec : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3)))
    (AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :
    Prop :=
  IsConnected X ∧ IsConnected (frontier X) ∧
  ∀ v ∈ K.vertices,
    (AK v).faces.Finite ∧ (AK v).space = Cpp v ∩ frontier X ∧
    IsCombinatorialManifoldWithBoundary 2 (AK v) ∧ IsConnected (AK v).space ∧
    (boundaryComplex 2 (AK v)).space = ⋃ e ∈ edgesAt K v, Ec e ∩ frontier X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasConnectedHandlePieces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasConnectedHandlePieces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasConnectedHandlePieces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasConnectedHandlePieces

end Vocabulary

end DifferentialGeometry.Topology.PiecewiseLinear
