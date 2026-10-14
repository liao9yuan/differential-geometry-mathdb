/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalClassification
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import Submission.DifferentialGeometry.Topology.Simplex.NormedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsCylindricalDiagram

theorem isTopologicalSolidTorus_of_eq_ends {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) : IsTopologicalSolidTorus S := by
  obtain ⟨e, _⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends
    hP.isPolyhedron.isCompact hends
  obtain ⟨p, hp⟩ := hP
  let d := hp.homeomorph.symm.trans (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
    (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  let c := Complex.orthonormalBasisOneI.repr
  have hc : Metric.sphere (0 : ℂ) 1 =
      c.toHomeomorph ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    change _ = c ⁻¹' _
    rw [c.preimage_sphere, map_zero]
  let circle := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
    (c.toHomeomorph.sets hc)
  exact ⟨e.trans (Homeomorph.prodCongr d circle)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_eq_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_eq_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_eq_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_eq_ends

theorem isTopologicalSolidTorus_of_isOrientable [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} (hP : IsPLBall 2 P)
    (M : Geometry.SimplicialComplex ℝ F) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f P M.space) : IsTopologicalSolidTorus M.space := by
  obtain ⟨g, hg, hends⟩ := hf.exists_endMap_id_of_isOrientable hP M hM hor
  exact hg.isTopologicalSolidTorus_of_eq_ends hP hends

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_isOrientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_isOrientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_isOrientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isTopologicalSolidTorus_of_isOrientable

end IsCylindricalDiagram

open _root_.Classical in
theorem isTopologicalSolidTorus_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) (hor : IsOrientable 3 K) :
    IsTopologicalSolidTorus (derivedNeighborhood K L).space := by
  obtain ⟨f, hf, hends⟩ := exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends
    K L hK hLK hL hconn hor
  exact hf.isTopologicalSolidTorus_of_eq_ends (isPLBall_stdSimplex 2) hends

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSolidTorus_derivedNeighborhood_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSolidTorus_derivedNeighborhood_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSolidTorus_derivedNeighborhood_circle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSolidTorus_derivedNeighborhood_circle

end DifferentialGeometry.Topology.PiecewiseLinear
