/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLTorus.isBicollared {T : Set (EuclideanSpace ℝ (Fin 3))}
    (hT : IsPLTorus T) : IsBicollared T := by
  obtain ⟨L, hLfin, hLcomb, hLc, hLspace⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hpoly : IsPolyhedralManifold (n := 3) 2 T := by
    have hLt : L.space ⊆
        (chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3))).target := by
      rw [chartAt_self_eq]
      exact _root_.Set.subset_univ _
    have h : IsPolyhedralManifold (n := 3) 2
        ((chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3))).symm ''
          L.space) :=
      ⟨⟨3, chartPieceOfComplex _ (chart_mem_atlas _ _) L hLt⟩, hLcomb⟩
    rw [← hLspace]
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, _root_.Set.image_id] using h
  exact hpoly.isBicollared (hpoly.isTwoSided (hLspace ▸ hLc))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.isBicollared then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.isBicollared"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.isBicollared ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLTorus.isBicollared

end DifferentialGeometry.Topology.PiecewiseLinear
