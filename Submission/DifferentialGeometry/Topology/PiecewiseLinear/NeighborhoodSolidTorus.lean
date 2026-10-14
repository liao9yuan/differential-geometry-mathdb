/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : Fin n ≃ L.faces,
      (⋃ i, (derivedNeighborhoodCell K (e i).val).space) = (derivedNeighborhood K L).space ∧
      (∀ i, IsPLBall 3 (derivedNeighborhoodCell K (e i).val).space) ∧
      (∀ i j, i ≠ j →
        (((derivedNeighborhoodCell K (e i).val).space ∩
          (derivedNeighborhoodCell K (e j).val).space).Nonempty ↔
            (SimpleGraph.cycleGraph n).Adj i j) ∧
        ((SimpleGraph.cycleGraph n).Adj i j →
          IsPLBall 2 ((derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space) ∧
          (derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space ⊆
              (boundaryComplex 3 (derivedNeighborhoodCell K (e i).val)).space ∧
          (derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space ⊆
              (boundaryComplex 3 (derivedNeighborhoodCell K (e j).val)).space)) ∧
      (∀ i j, i ≠ j → ¬ (SimpleGraph.cycleGraph n).Adj i j →
        Disjoint (derivedNeighborhoodCell K (e i).val).space
          (derivedNeighborhoodCell K (e j).val).space) ∧
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        Disjoint ((derivedNeighborhoodCell K (e i).val).space ∩
          (derivedNeighborhoodCell K (e j).val).space)
          (derivedNeighborhoodCell K (e k).val).space := by
  obtain ⟨n, hn, e, hcover, hball, hpair⟩ :=
    exists_cyclic_derivedNeighborhoodCell_decomposition K L hK hLK hL hconn
  refine ⟨n, hn, e, hcover, hball, hpair, ?_, ?_⟩
  · intro i j hij hnot
    exact disjoint_left.mpr fun x hxi hxj => hnot ((hpair i j hij).1.mp ⟨x, hxi, hxj⟩)
  · intro i j k hij hik hjk
    exact disjoint_derivedNeighborhoodCell_inter_of_card_le_two K L hLK
      (fun s hs => hL.card_le L hs) (e i).property (e j).property (e k).property
      (fun h => hij (e.injective (Subtype.ext h)))
      (fun h => hik (e.injective (Subtype.ext h)))
      (fun h => hjk (e.injective (Subtype.ext h)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint

open _root_.Classical in
theorem isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space)
    (hor : @IsOrientable E _ _ 3 (derivedNeighborhood K L)
      (derivedNeighborhood_faces_finite K L).to_subtype) :
    IsCombinatorialSolidTorus (derivedNeighborhood K L).space := by
  let _ : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  obtain ⟨f, hf⟩ := exists_cylindricalDiagram_derivedNeighborhood_circle K L hK hLK hL hconn
  have htor := hf.isTopologicalSolidTorus_of_isOrientable (isPLBall_stdSimplex 2)
    (derivedNeighborhood K L) (hK.derivedNeighborhood L) hor
  obtain ⟨n, hn, e, hcover, hball, hpair, _, _⟩ :=
    exists_cyclic_derivedNeighborhoodCell_decomposition_disjoint K L hK hLK hL hconn
  exact ⟨htor, n, hn, fun i => derivedNeighborhoodCell K (e i).val,
    fun i => derivedNeighborhoodCell_faces_finite K (e i).val, hcover, hball, hpair⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable

open _root_.Classical in
theorem isCombinatorialSolidTorus_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) (hor : IsOrientable 3 K) :
    IsCombinatorialSolidTorus (derivedNeighborhood K L).space := by
  obtain ⟨horN, _⟩ := exists_cylindricalDiagram_isOrientable_derivedNeighborhood_circle
    K L hK hLK hL hconn hor
  exact isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable K L hK hLK hL hconn horN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_derivedNeighborhood_circle

end DifferentialGeometry.Topology.PiecewiseLinear
