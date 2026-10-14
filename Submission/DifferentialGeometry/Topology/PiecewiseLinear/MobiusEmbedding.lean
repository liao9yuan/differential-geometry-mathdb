/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MobiusManifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MobiusMappingTorus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsOrientable.of_isPLHomeomorphOn_subset
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] {n : ℕ} {Q : Set E} {f : F → E}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L) (h : IsOrientable n K)
    (hf : IsPLHomeomorphOn f L.space Q) (hQK : Q ⊆ K.space) : IsOrientable n L := by
  have hQ : IsPolyhedron Q := by
    rw [← hf.image_eq]
    exact (isPolyhedron_space L).image_of_isPiecewiseAffineOn
      hf.isPiecewiseAffineOn hf.bijOn.injOn
  obtain ⟨R, hR, hRfin, hRQ⟩ := exists_isSubdivision_restrict_space K hQ hQK
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (restrict R Q).faces := (restrict_faces_finite R Q).to_subtype
  have hf' : IsPLHomeomorphOn f L.space (restrict R Q).space := hRQ.symm ▸ hf
  have hLo := IsOrientable.of_le R (restrict R Q) (restrict_faces_subset R Q)
    (hK.of_isSubdivision hR) (hL.of_isPLHomeomorphOn hf') (h.subdivision hK hR)
  exact (isOrientable_iff_of_isPLHomeomorphOn hL hf').mpr hLo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_isPLHomeomorphOn_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_isPLHomeomorphOn_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_isPLHomeomorphOn_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_isPLHomeomorphOn_subset

theorem IsOrientable.of_space_subset
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {n : ℕ} (hLK : L.space ⊆ K.space)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (h : IsOrientable n K) : IsOrientable n L :=
  h.of_isPLHomeomorphOn_subset K L hK hL
    (isPolyhedron_space L).isPLHomeomorphOn_id hLK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_space_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_space_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_space_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsOrientable.of_space_subset

theorem not_isPLHomeomorphOn_mobiusComplex_of_isOrientable
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (h : IsOrientable 2 K)
    {Q : Set E} (hQK : Q ⊆ K.space) (j : (Fin 5 → ℝ) → E) :
    ¬ IsPLHomeomorphOn j mobiusComplex.space Q := by
  intro hj
  exact not_isOrientable_mobiusComplex
    (h.of_isPLHomeomorphOn_subset K mobiusComplex hK
      isCombinatorialManifoldWithBoundary_mobiusComplex hj hQK)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.not_isPLHomeomorphOn_mobiusComplex_of_isOrientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.not_isPLHomeomorphOn_mobiusComplex_of_isOrientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.not_isPLHomeomorphOn_mobiusComplex_of_isOrientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.not_isPLHomeomorphOn_mobiusComplex_of_isOrientable

theorem isPLCirclePositive_of_isOrientable_cylindricalDiagram
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (h : IsOrientable 2 K)
    {S : Set E} (hS : IsPLSphere 1 S) {T : Set F} {f : E × ℝ → F}
    (hf : IsCylindricalDiagram f S T) (hTK : T ⊆ K.space) {v : E → E}
    (hv : IsPLHomeomorphOn v S S) (hfv : ∀ x ∈ S, f (x, 1) = f (v x, 0)) :
    IsPLCirclePositive S v := by
  by_contra hnv
  obtain ⟨Q, j, hj, hQT⟩ :=
    exists_isPLHomeomorphOn_mobiusComplex_of_not_isPLCirclePositive hS hf hv hnv hfv
  exact not_isPLHomeomorphOn_mobiusComplex_of_isOrientable K hK h (hQT.trans hTK) j hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_of_isOrientable_cylindricalDiagram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_of_isOrientable_cylindricalDiagram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_of_isOrientable_cylindricalDiagram ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_of_isOrientable_cylindricalDiagram

end DifferentialGeometry.Topology.PiecewiseLinear
