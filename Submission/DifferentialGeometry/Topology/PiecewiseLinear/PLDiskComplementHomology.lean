/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.CompactChainSupport
import Submission.DifferentialGeometry.Topology.Homology.ComplementHomeomorphHomology
import Submission.DifferentialGeometry.Topology.Homology.ConvexComplementFirstHomology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDiskNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_ball_neighborhood_of_disk
    {D U : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsPLBall 2 D)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ N : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 N ∧ D ⊆ N ∧ N ⊆ U := by
  classical
  obtain ⟨T, hT, hTcard, hDT⟩ := exists_affineIndependent_openSimplex_superset 3 (by simp)
    hD.isPolyhedron.isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKsp : K.space = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKsp.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hDK : D ⊆ K.space := by
    rw [hKsp]
    exact hDT.trans (openSimplex_subset_convexHull T)
  obtain ⟨K', M, -, hK'fin, hMK', hM, hMU, hMnhds⟩ :=
    hKball.isCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood
      hD.isPolyhedron.isCompact hDK hU hDU
  let _ : Finite M.faces := (hK'fin.subset hMK').to_subtype
  have hDM : D ⊆ M.space := fun x hx => mem_of_mem_nhdsWithin (hDK hx) (hMnhds x hx)
  obtain ⟨R, A, -, -, -, -, -, hN, hDN, hNM, -⟩ :=
    hM.exists_isPLBall_derivedNeighborhood_disk hD hDM
  exact ⟨_, hN, hDN, hNM.trans hMU⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_ball_neighborhood_of_disk
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_ball_neighborhood_of_disk target :: scope.openDecls } }

theorem IsPLBall.subsingleton_integralFirstHomology_complement
    {B : Set (EuclideanSpace ℝ (Fin 3))} (hB : IsPLBall 3 B) :
    Subsingleton (integralSingularHomology 1 (Bᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨T, e, hT, hcard, -, he, -⟩ :=
    hB.isPLSphere_frontier.isSimplyEmbedded.2 _root_.Set.univ convex_univ isOpen_univ (_root_.Set.subset_univ _)
  have hP := (hasPushProperty_convexHull_simplex T hT hcard).1
  have hfront : frontier (e '' B) =
      frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [← e.image_frontier, he]
  have hint : (interior (e '' B)).Nonempty := by
    rw [← e.image_interior]
    exact hB.interior_nonempty.image e
  have heq := DifferentialGeometry.Analysis.IsCompact.eq_of_frontier_eq_convex_closed
    (hB.isPolyhedron.isCompact.image e.continuous) hint (convex_convexHull ℝ _)
    hP.isPolyhedron.isCompact.isClosed hfront
  apply (subsingleton_integralComplementHomology_iff 1 e B).mpr
  rw [heq]
  obtain ⟨p, hp⟩ := hP.nonempty
  exact subsingleton_integralFirstHomology_complement_of_bounded_starConvex hp
    ((convex_convexHull ℝ _).starConvex hp) hP.isPolyhedron.isCompact.isBounded

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.subsingleton_integralFirstHomology_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.subsingleton_integralFirstHomology_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.subsingleton_integralFirstHomology_complement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.subsingleton_integralFirstHomology_complement

namespace TorusLinking

theorem subsingleton_firstHomology_complement_of_isPLDisk
    {Δ : Set (EuclideanSpace ℝ (Fin 3))} (hΔ : IsPLBall 2 Δ) :
    Subsingleton (integralSingularHomology 1 (Δᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  apply subsingleton_integralSingularHomology_of_compact_carriers 0
  intro K hK hKD
  obtain ⟨N, hN, hDN, hNK⟩ := exists_ball_neighborhood_of_disk hΔ hK.isClosed.isOpen_compl
    (fun x hx hKx => hKD hKx hx)
  exact ⟨Nᶜ, fun x hx hNx => hNK hNx hx, compl_subset_compl.mpr hDN,
    hN.subsingleton_integralFirstHomology_complement⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking.subsingleton_firstHomology_complement_of_isPLDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking.subsingleton_firstHomology_complement_of_isPLDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking.subsingleton_firstHomology_complement_of_isPLDisk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking.subsingleton_firstHomology_complement_of_isPLDisk

end TorusLinking

end DifferentialGeometry.Topology.PiecewiseLinear
