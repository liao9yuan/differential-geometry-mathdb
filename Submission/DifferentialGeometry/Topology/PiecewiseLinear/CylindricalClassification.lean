/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMonodromy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E}

open _root_.Classical in
theorem isPLPseudoIsotopicToId_endMap (hP : IsPLBall 2 P)
    (M : Geometry.SimplicialComplex ℝ F) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f P M.space) {u : E → E}
    (hu : IsPLHomeomorphOn u P P) (hfu : ∀ x ∈ P, f (x, 0) = f (u x, 1)) :
    IsPLPseudoIsotopicToId u P := by
  obtain ⟨D, hDfin, hDspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite D.faces := hDfin.to_subtype
  have hD : IsPLBall 2 D.space := hDspace.symm ▸ hP
  have hf' : IsCylindricalDiagram f D.space M.space := hDspace.symm ▸ hf
  have hu' : IsPLHomeomorphOn u D.space D.space := by rwa [hDspace]
  have hfu' : ∀ x ∈ D.space, f (x, 0) = f (u x, 1) := by rwa [hDspace]
  have hpos := hf'.boundary_isPLCirclePositive_of_bottom_eq_top D M hD hM hor hu' hfu'
  have h := isPLPseudoIsotopicToId_of_boundary_isPLCirclePositive D hD hu' hpos
  rwa [hDspace] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLPseudoIsotopicToId_endMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLPseudoIsotopicToId_endMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLPseudoIsotopicToId_endMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLPseudoIsotopicToId_endMap

theorem exists_endMap_id_of_isOrientable (hP : IsPLBall 2 P)
    (M : Geometry.SimplicialComplex ℝ F) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f P M.space) :
    ∃ g : E × ℝ → F, IsCylindricalDiagram g P M.space ∧
      ∀ x ∈ P, g (x, 0) = g (x, 1) := by
  obtain ⟨u, hu, hfu⟩ := hf.exists_isPLHomeomorphOn_endMap hP.isPolyhedron
  exact hf.exists_endMap_id_of_pseudoIsotopicToId hu hfu
    (hf.isPLPseudoIsotopicToId_endMap hP M hM hor hu hfu)
    hP.isPolyhedron.isPLHomeomorphOn_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_endMap_id_of_isOrientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_endMap_id_of_isOrientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_endMap_id_of_isOrientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_endMap_id_of_isOrientable

end IsCylindricalDiagram

theorem exists_isPLHomeomorphOn_of_isOrientable_cylindricalDiagrams
    {E' G : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {P : Set E} {Q : Set E'} (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q)
    (M : Geometry.SimplicialComplex ℝ F) (N : Geometry.SimplicialComplex ℝ G)
    [Finite M.faces] [Finite N.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hN : IsCombinatorialManifoldWithBoundary 3 N)
    (horM : IsOrientable 3 M) (horN : IsOrientable 3 N)
    {f : E × ℝ → F} {g : E' × ℝ → G}
    (hf : IsCylindricalDiagram f P M.space) (hg : IsCylindricalDiagram g Q N.space) :
    ∃ H : F → G, IsPLHomeomorphOn H M.space N.space := by
  obtain ⟨u, hu, hfu⟩ := hf.exists_isPLHomeomorphOn_endMap hP.isPolyhedron
  obtain ⟨v, hv, hgv⟩ := hg.exists_isPLHomeomorphOn_endMap hQ.isPolyhedron
  have hisof := hf.isPLPseudoIsotopicToId_endMap hP M hM horM hu hfu
  have hisog := hg.isPLPseudoIsotopicToId_endMap hQ N hN horN hv hgv
  have hQpoly := hQ.isPolyhedron
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  exact exists_isPLHomeomorphOn_of_endMaps_pseudoIsotopicToId hf hg
    hQpoly hu hv hfu hgv hisof hisog (hq.symm.trans hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_isOrientable_cylindricalDiagrams then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_isOrientable_cylindricalDiagrams"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_isOrientable_cylindricalDiagrams ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_isOrientable_cylindricalDiagrams

open _root_.Classical in
theorem exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) (hor : IsOrientable 3 K) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsCylindricalDiagram φ (stdSimplex ℝ (Fin 3)) (derivedNeighborhood K L).space ∧
        ∀ x ∈ stdSimplex ℝ (Fin 3), φ (x, 0) = φ (x, 1) := by
  let _ : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  obtain ⟨horN, f, hf⟩ := exists_cylindricalDiagram_isOrientable_derivedNeighborhood_circle
    K L hK hLK hL hconn hor
  exact hf.exists_endMap_id_of_isOrientable (isPLBall_stdSimplex 2)
    (derivedNeighborhood K L) (hK.derivedNeighborhood L) horN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends

end DifferentialGeometry.Topology.PiecewiseLinear
