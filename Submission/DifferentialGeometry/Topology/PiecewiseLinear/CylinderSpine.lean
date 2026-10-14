/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CellGluingSphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.isSpine_of_eq_ends
    {f : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {P : Set (EuclideanSpace ℝ (Fin 2))} {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P) :
    IsSpine S (f '' ({a} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨r, hr⟩ := hP
  have hcell := hr.isTopologicalCellWithInterior
  rw [hr.image_stdSimplexBoundary_eq_frontier, self_sdiff_frontier] at hcell
  obtain ⟨d, hd⟩ := hcell
  rw [hd] at ha
  obtain ⟨b, ⟨u, hu, hdu⟩, hba⟩ := ha
  have hdua : (d u : EuclideanSpace ℝ (Fin 2)) = a :=
    (congrArg Subtype.val hdu).trans hba
  obtain ⟨e, he⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends
    (show IsPLBall 2 P from ⟨r, hr⟩).isPolyhedron.isCompact hends
  let T := (d.prodCongr planarCircleParam.symm).trans e.symm
  have huinterior : (u : EuclideanSpace ℝ (Fin 2)) ∈
      interior (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [interior_closedBall _ one_ne_zero]
    exact mem_ball_zero_iff.mpr hu
  refine ⟨T, u, huinterior, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hxa : x = a := hx
    subst x
    let q := (u, planarCircleParam (t : loopCircle))
    refine ⟨T q, ⟨q, rfl, rfl⟩, ?_⟩
    change (e.symm (d u, planarCircleParam.symm (planarCircleParam (t : loopCircle))) :
      EuclideanSpace ℝ (Fin 3)) = f (a, t)
    rw [Homeomorph.symm_apply_apply, he (d u) ⟨t, ht⟩, hdua]
  · rintro ⟨b, ⟨q, hq, rfl⟩, rfl⟩
    have hqu : q.1 = u := Subtype.ext hq
    obtain ⟨t, ht, htc⟩ := exists_lift_mem_Ico (planarCircleParam.symm q.2)
    refine ⟨(a, t), ⟨rfl, ht.1, ht.2.le⟩, ?_⟩
    change f (a, t) = (e.symm (d q.1, planarCircleParam.symm q.2) :
      EuclideanSpace ℝ (Fin 3))
    rw [hqu, ← htc, he (d u) ⟨t, ht.1, ht.2.le⟩, hdua]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isSpine_of_eq_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isSpine_of_eq_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isSpine_of_eq_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isSpine_of_eq_ends

end DifferentialGeometry.Topology.PiecewiseLinear
