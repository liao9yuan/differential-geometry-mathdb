/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Product
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import Submission.DifferentialGeometry.Topology.PlanarJordan.StripExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.Schoenflies (Plane)
open _root_.Submission.DifferentialGeometry.Topology.PlanarJordan

theorem isHPolytope_planeRect (a b c d : ℝ) : IsHPolytope (planeRect a b c d) := by
  let L : Plane ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have heq : L.symm.toLinearEquiv.toAffineEquiv '' (_root_.Set.Icc a b ×ˢ _root_.Set.Icc c d) =
      planeRect a b c d := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h0 : (L.symm w) 0 = w.1 := congrArg Prod.fst (L.apply_symm_apply w)
      have h1 : (L.symm w) 1 = w.2 := congrArg Prod.snd (L.apply_symm_apply w)
      change a ≤ (L.symm w) 0 ∧ (L.symm w) 0 ≤ b ∧
        c ≤ (L.symm w) 1 ∧ (L.symm w) 1 ≤ d
      rw [h0, h1]
      exact ⟨hw.1.1, hw.1.2, hw.2.1, hw.2.2⟩
    · intro hv
      exact ⟨L v, ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩, L.symm_apply_apply v⟩
  rw [← heq]
  exact (isHPolytope_Icc.prod isHPolytope_Icc).image_affineEquiv _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_planeRect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_planeRect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_planeRect ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_planeRect

theorem exists_simplicialComplex_planeRect (a b c d : ℝ) :
    ∃ K : Geometry.SimplicialComplex ℝ Plane,
      K.faces.Finite ∧ K.space = planeRect a b c d :=
  (isHPolytope_planeRect a b c d).isPolyhedron.exists_simplicialComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_simplicialComplex_planeRect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_simplicialComplex_planeRect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_simplicialComplex_planeRect ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_simplicialComplex_planeRect

end DifferentialGeometry.Topology.PiecewiseLinear
